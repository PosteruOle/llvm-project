//===- AggressiveInstCombine.cpp ------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the aggressive expression pattern combiner classes.
// Currently, it handles expression patterns for:
//  * Truncate instruction
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "AggressiveInstCombineInternal.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"
#include "llvm/Transforms/Utils/Local.h"
#include <cstring>
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/BasicBlock.h"
#include <cassert>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IntrinsicsRISCV.h"

using namespace llvm;
using namespace PatternMatch;

#define DEBUG_TYPE "aggressive-instcombine"

STATISTIC(NumAnyOrAllBitsSet, "Number of any/all-bits-set patterns folded");
STATISTIC(NumGuardedRotates,
          "Number of guarded rotates transformed into funnel shifts");
STATISTIC(NumGuardedFunnelShifts,
          "Number of guarded funnel shifts transformed into funnel shifts");
STATISTIC(NumPopCountRecognized, "Number of popcount idioms recognized");

/*
Petar's potential insertion!
STATISTIC(NumReverseRecognized, "Number of reverse function recognized");
*/

static cl::opt<unsigned> MaxInstrsToScan(
    "aggressive-instcombine-max-scan-instrs", cl::init(64), cl::Hidden,
    cl::desc("Max number of instructions to scan for aggressive instcombine."));

static cl::opt<bool> UseOptionOne(
    "use-opt-one", cl::init(false), cl::Hidden,
    cl::desc("Using option one!"));    

static cl::opt<bool> UseOptionTwo(
    "use-opt-two", cl::init(false), cl::Hidden,
    cl::desc("Using option two!"));  

/// Match a pattern for a bitwise funnel/rotate operation that partially guards
/// against undefined behavior by branching around the funnel-shift/rotation
/// when the shift amount is 0.
static bool foldGuardedFunnelShift(Instruction &I, const DominatorTree &DT) {
  if (I.getOpcode() != Instruction::PHI || I.getNumOperands() != 2)
    return false;

  // As with the one-use checks below, this is not strictly necessary, but we
  // are being cautious to avoid potential perf regressions on targets that
  // do not actually have a funnel/rotate instruction (where the funnel shift
  // would be expanded back into math/shift/logic ops).
  if (!isPowerOf2_32(I.getType()->getScalarSizeInBits()))
    return false;

  // Match V to funnel shift left/right and capture the source operands and
  // shift amount.
  auto matchFunnelShift = [](Value *V, Value *&ShVal0, Value *&ShVal1,
                             Value *&ShAmt) {
    unsigned Width = V->getType()->getScalarSizeInBits();

    // fshl(ShVal0, ShVal1, ShAmt)
    //  == (ShVal0 << ShAmt) | (ShVal1 >> (Width -ShAmt))
    if (match(V, m_OneUse(m_c_Or(
                     m_Shl(m_Value(ShVal0), m_Value(ShAmt)),
                     m_LShr(m_Value(ShVal1),
                            m_Sub(m_SpecificInt(Width), m_Deferred(ShAmt))))))) {
        return Intrinsic::fshl;
    }

    // fshr(ShVal0, ShVal1, ShAmt)
    //  == (ShVal0 >> ShAmt) | (ShVal1 << (Width - ShAmt))
    if (match(V,
              m_OneUse(m_c_Or(m_Shl(m_Value(ShVal0), m_Sub(m_SpecificInt(Width),
                                                           m_Value(ShAmt))),
                              m_LShr(m_Value(ShVal1), m_Deferred(ShAmt)))))) {
        return Intrinsic::fshr;
    }

    return Intrinsic::not_intrinsic;
  };

  // One phi operand must be a funnel/rotate operation, and the other phi
  // operand must be the source value of that funnel/rotate operation:
  // phi [ rotate(RotSrc, ShAmt), FunnelBB ], [ RotSrc, GuardBB ]
  // phi [ fshl(ShVal0, ShVal1, ShAmt), FunnelBB ], [ ShVal0, GuardBB ]
  // phi [ fshr(ShVal0, ShVal1, ShAmt), FunnelBB ], [ ShVal1, GuardBB ]
  PHINode &Phi = cast<PHINode>(I);
  unsigned FunnelOp = 0, GuardOp = 1;
  Value *P0 = Phi.getOperand(0), *P1 = Phi.getOperand(1);
  Value *ShVal0, *ShVal1, *ShAmt;
  Intrinsic::ID IID = matchFunnelShift(P0, ShVal0, ShVal1, ShAmt);
  if (IID == Intrinsic::not_intrinsic ||
      (IID == Intrinsic::fshl && ShVal0 != P1) ||
      (IID == Intrinsic::fshr && ShVal1 != P1)) {
    IID = matchFunnelShift(P1, ShVal0, ShVal1, ShAmt);
    if (IID == Intrinsic::not_intrinsic ||
        (IID == Intrinsic::fshl && ShVal0 != P0) ||
        (IID == Intrinsic::fshr && ShVal1 != P0))
      return false;
    assert((IID == Intrinsic::fshl || IID == Intrinsic::fshr) &&
           "Pattern must match funnel shift left or right");
    std::swap(FunnelOp, GuardOp);
  }

  // The incoming block with our source operand must be the "guard" block.
  // That must contain a cmp+branch to avoid the funnel/rotate when the shift
  // amount is equal to 0. The other incoming block is the block with the
  // funnel/rotate.
  BasicBlock *GuardBB = Phi.getIncomingBlock(GuardOp);
  BasicBlock *FunnelBB = Phi.getIncomingBlock(FunnelOp);
  Instruction *TermI = GuardBB->getTerminator();

  // Ensure that the shift values dominate each block.
  if (!DT.dominates(ShVal0, TermI) || !DT.dominates(ShVal1, TermI))
    return false;

  ICmpInst::Predicate Pred;
  BasicBlock *PhiBB = Phi.getParent();
  if (!match(TermI, m_Br(m_ICmp(Pred, m_Specific(ShAmt), m_ZeroInt()),
                         m_SpecificBB(PhiBB), m_SpecificBB(FunnelBB))))
    return false;

  if (Pred != CmpInst::ICMP_EQ)
    return false;

  IRBuilder<> Builder(PhiBB, PhiBB->getFirstInsertionPt());

  if (ShVal0 == ShVal1)
    ++NumGuardedRotates;
  else
    ++NumGuardedFunnelShifts;

  // If this is not a rotate then the select was blocking poison from the
  // 'shift-by-zero' non-TVal, but a funnel shift won't - so freeze it.
  bool IsFshl = IID == Intrinsic::fshl;
  if (ShVal0 != ShVal1) {
    if (IsFshl && !llvm::isGuaranteedNotToBePoison(ShVal1))
      ShVal1 = Builder.CreateFreeze(ShVal1);
    else if (!IsFshl && !llvm::isGuaranteedNotToBePoison(ShVal0))
      ShVal0 = Builder.CreateFreeze(ShVal0);
  }

  // We matched a variation of this IR pattern:
  // GuardBB:
  //   %cmp = icmp eq i32 %ShAmt, 0
  //   br i1 %cmp, label %PhiBB, label %FunnelBB
  // FunnelBB:
  //   %sub = sub i32 32, %ShAmt
  //   %shr = lshr i32 %ShVal1, %sub
  //   %shl = shl i32 %ShVal0, %ShAmt
  //   %fsh = or i32 %shr, %shl
  //   br label %PhiBB
  // PhiBB:
  //   %cond = phi i32 [ %fsh, %FunnelBB ], [ %ShVal0, %GuardBB ]
  // -->
  // llvm.fshl.i32(i32 %ShVal0, i32 %ShVal1, i32 %ShAmt)
  Function *F = Intrinsic::getDeclaration(Phi.getModule(), IID, Phi.getType());
  Phi.replaceAllUsesWith(Builder.CreateCall(F, {ShVal0, ShVal1, ShAmt}));
  return true;
}

/// This is used by foldAnyOrAllBitsSet() to capture a source value (Root) and
/// the bit indexes (Mask) needed by a masked compare. If we're matching a chain
/// of 'and' ops, then we also need to capture the fact that we saw an
/// "and X, 1", so that's an extra return value for that case.
struct MaskOps {
  Value *Root = nullptr;
  APInt Mask;
  bool MatchAndChain;
  bool FoundAnd1 = false;

  MaskOps(unsigned BitWidth, bool MatchAnds)
      : Mask(APInt::getZero(BitWidth)), MatchAndChain(MatchAnds) {}
};

/// This is a recursive helper for foldAnyOrAllBitsSet() that walks through a
/// chain of 'and' or 'or' instructions looking for shift ops of a common source
/// value. Examples:
///   or (or (or X, (X >> 3)), (X >> 5)), (X >> 8)
/// returns { X, 0x129 }
///   and (and (X >> 1), 1), (X >> 4)
/// returns { X, 0x12 }
static bool matchAndOrChain(Value *V, MaskOps &MOps) {
  Value *Op0, *Op1;
  if (MOps.MatchAndChain) {
    // Recurse through a chain of 'and' operands. This requires an extra check
    // vs. the 'or' matcher: we must find an "and X, 1" instruction somewhere
    // in the chain to know that all of the high bits are cleared.
    if (match(V, m_And(m_Value(Op0), m_One()))) {
      MOps.FoundAnd1 = true;
      return matchAndOrChain(Op0, MOps);
    }
    if (match(V, m_And(m_Value(Op0), m_Value(Op1))))
      return matchAndOrChain(Op0, MOps) && matchAndOrChain(Op1, MOps);
  } else {
    // Recurse through a chain of 'or' operands.
    if (match(V, m_Or(m_Value(Op0), m_Value(Op1))))
      return matchAndOrChain(Op0, MOps) && matchAndOrChain(Op1, MOps);
  }

  // We need a shift-right or a bare value representing a compare of bit 0 of
  // the original source operand.
  Value *Candidate;
  const APInt *BitIndex = nullptr;
  if (!match(V, m_LShr(m_Value(Candidate), m_APInt(BitIndex))))
    Candidate = V;

  // Initialize result source operand.
  if (!MOps.Root)
    MOps.Root = Candidate;

  // The shift constant is out-of-range? This code hasn't been simplified.
  if (BitIndex && BitIndex->uge(MOps.Mask.getBitWidth()))
    return false;

  // Fill in the mask bit derived from the shift constant.
  MOps.Mask.setBit(BitIndex ? BitIndex->getZExtValue() : 0);
  return MOps.Root == Candidate;
}

/// Match patterns that correspond to "any-bits-set" and "all-bits-set".
/// These will include a chain of 'or' or 'and'-shifted bits from a
/// common source value:
/// and (or  (lshr X, C), ...), 1 --> (X & CMask) != 0
/// and (and (lshr X, C), ...), 1 --> (X & CMask) == CMask
/// Note: "any-bits-clear" and "all-bits-clear" are variations of these patterns
/// that differ only with a final 'not' of the result. We expect that final
/// 'not' to be folded with the compare that we create here (invert predicate).
static bool foldAnyOrAllBitsSet(Instruction &I) {
  // The 'any-bits-set' ('or' chain) pattern is simpler to match because the
  // final "and X, 1" instruction must be the final op in the sequence.
  bool MatchAllBitsSet;
  if (match(&I, m_c_And(m_OneUse(m_And(m_Value(), m_Value())), m_Value())))
    MatchAllBitsSet = true;
  else if (match(&I, m_And(m_OneUse(m_Or(m_Value(), m_Value())), m_One())))
    MatchAllBitsSet = false;
  else
    return false;

  MaskOps MOps(I.getType()->getScalarSizeInBits(), MatchAllBitsSet);
  if (MatchAllBitsSet) {
    if (!matchAndOrChain(cast<BinaryOperator>(&I), MOps) || !MOps.FoundAnd1)
      return false;
  } else {
    if (!matchAndOrChain(cast<BinaryOperator>(&I)->getOperand(0), MOps))
      return false;
  }

  // The pattern was found. Create a masked compare that replaces all of the
  // shift and logic ops.
  IRBuilder<> Builder(&I);
  Constant *Mask = ConstantInt::get(I.getType(), MOps.Mask);
  Value *And = Builder.CreateAnd(MOps.Root, Mask);
  Value *Cmp = MatchAllBitsSet ? Builder.CreateICmpEQ(And, Mask)
                               : Builder.CreateIsNotNull(And);
  Value *Zext = Builder.CreateZExt(Cmp, I.getType());
  I.replaceAllUsesWith(Zext);
  ++NumAnyOrAllBitsSet;
  return true;
}
//---------------------------------------------------------------------------------------------------------------------------------------
// Petar's code!
//unsigned reverse(unsigned x) {
//   x = ((x & 0x55555555) <<  1) | ((x >>  1) & 0x55555555);               ?
//   x = ((x & 0x33333333) <<  2) | ((x >>  2) & 0x33333333);               .
//   x = ((x & 0x0F0F0F0F) <<  4) | ((x >>  4) & 0x0F0F0F0F);               .
//   x = (x << 24) | ((x & 0xFF00) << 8) | ((x >> 8) & 0xFF00) | (x >> 24); .  
//   return x;
//}

// int popcount(unsigned int i) {
//   i = i - ((i >> 1) & 0x55555555);
//   i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
//   i = ((i + (i >> 4)) & 0x0F0F0F0F);
//   return (i * 0x01010101) >> 24;

static bool tryToRecognizeReverseFunction(Instruction &I){
  if(I.getOpcode()!=Instruction::Or)
    return false;
  Type *Ty = I.getType();
  if (!Ty->isIntOrIntVectorTy())
    return false;
  
  unsigned Len = Ty->getScalarSizeInBits();
  // FIXME: fix Len == 8 and other irregular type lengths.
  if (!(Len <= 128 && Len > 8 && Len % 8 == 0))
    return false;

  APInt Mask55 = APInt::getSplat(Len, APInt(8, 0x55));
  APInt Mask33 = APInt::getSplat(Len, APInt(8, 0x33));
  APInt Mask0F = APInt::getSplat(Len, APInt(8, 0x0F));
  APInt Mask01 = APInt::getSplat(Len, APInt(8, 0x01));
  APInt MaskShift = APInt(Len, Len - 8); 
 
  //Value *Op0 = I.getOperand(0);
  //Value *Op1 = I.getOperand(1);
  Value *MulOp0;
  
  //Petar's insertion! Aditional variables!
  //Value *value1; 

  // I need to change this part!
  // Matching  "(x << 24) | ((x & 0xFF00) << 8) | ((x >> 8) & 0xFF00) | (x >> 24))" <- reverse function instruction! (Petar)
  if ((match(MulOp0, m_Or(m_Shl(m_Value(MulOp0), m_SpecificInt(MaskShift)),
      m_Or(m_Shl(m_And(m_Deferred(MulOp0), m_SpecificInt(65280)), m_SpecificInt(8)), 
      m_Or(m_And(m_LShr(m_Deferred(MulOp0), m_SpecificInt(8)), m_SpecificInt(65280)), m_LShr(m_Deferred(MulOp0), m_SpecificInt(24)))))))) {
        
    // I hope we recognised the previous instruction! (Petar)
    //Value *ShiftOp0;

    // matching ((x & 0x0F0F0F0F) <<  4) | ((x >>  4) & 0x0F0F0F0F) <- reverse function instruction!
    if(match(MulOp0, m_Or(m_Shl(m_And(m_Value(MulOp0), m_SpecificInt(Mask0F)), m_SpecificInt(4)), 
      m_And(m_LShr(m_Deferred(MulOp0), m_SpecificInt(4)), m_SpecificInt(Mask0F))))){

      // I hope we recognised the previous instruction! (Petar)
      //Value *AndOp0;

      // Matching ((x & 0x33333333) <<  2) | ((x >>  2) & 0x33333333) <- reverse function instruction! (Petar)
      if (match(MulOp0, m_Or(m_Shl(m_And(m_Value(MulOp0), m_SpecificInt(Mask33)), m_SpecificInt(2)), 
        m_And(m_LShr(m_Deferred(MulOp0), m_SpecificInt(2)), m_SpecificInt(Mask33))))) {
        
        // I hope we recognised the previous instruction! (Petar)
        //Value *Root, *SubOp1;

        // Matching "((x & 0x55555555) <<  1) | ((x >>  1) & 0x55555555))" <- reverse function instruction! (Petar)
        if (match(MulOp0, m_Or(m_Shl(m_And(m_Value(MulOp0), m_SpecificInt(Mask55)), m_SpecificInt(1)), 
          m_And(m_LShr(m_Deferred(MulOp0), m_SpecificInt(1)), m_SpecificInt(Mask55))))) {
          
          // I hope we recognised the previous instruction! (Petar)
          
          //LLVM_DEBUG(dbgs() << "Recognized reverse function!\n");
          //IRBuilder<> Builder(&I);
          
          //Function *Func = Intrinsic::getDeclaration(I.getModule(), Intrinsic::ctpop, I.getType());
          
          //I.replaceAllUsesWith(Builder.CreateCall(Func, {Root}));
          //++NumReverseRecognized;
          
          return true;
        }
      }
    }       
  }
}  

//---------------------------------------------------------------------------------------------------------------------------------------


// Try to recognize below function as popcount intrinsic.
// This is the "best" algorithm from
// http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
// Also used in TargetLowering::expandCTPOP().
//
// int popcount(unsigned int i) {
//   i = i - ((i >> 1) & 0x55555555);
//   i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
//   i = ((i + (i >> 4)) & 0x0F0F0F0F);
//   return (i * 0x01010101) >> 24;
// }
static bool tryToRecognizePopCount(Instruction &I) {
  if (I.getOpcode() != Instruction::LShr)
    return false;

  Type *Ty = I.getType();
  if (!Ty->isIntOrIntVectorTy())
    return false;

  unsigned Len = Ty->getScalarSizeInBits();
  // FIXME: fix Len == 8 and other irregular type lengths.
  if (!(Len <= 128 && Len > 8 && Len % 8 == 0))
    return false;

  APInt Mask55 = APInt::getSplat(Len, APInt(8, 0x55));
  APInt Mask33 = APInt::getSplat(Len, APInt(8, 0x33));
  APInt Mask0F = APInt::getSplat(Len, APInt(8, 0x0F));
  APInt Mask01 = APInt::getSplat(Len, APInt(8, 0x01));
  APInt MaskShift = APInt(Len, Len - 8);

  Value *Op0 = I.getOperand(0);
  Value *Op1 = I.getOperand(1);
  Value *MulOp0;
  // Matching "(i * 0x01010101...) >> 24".
  if ((match(Op0, m_Mul(m_Value(MulOp0), m_SpecificInt(Mask01)))) &&
      match(Op1, m_SpecificInt(MaskShift))) {
    Value *ShiftOp0;
    // Matching "((i + (i >> 4)) & 0x0F0F0F0F...)".
    if (match(MulOp0, m_And(m_c_Add(m_LShr(m_Value(ShiftOp0), m_SpecificInt(4)),
                                    m_Deferred(ShiftOp0)),
                            m_SpecificInt(Mask0F)))) {
      Value *AndOp0;
      // Matching "(i & 0x33333333...) + ((i >> 2) & 0x33333333...)".
      if (match(ShiftOp0,
                m_c_Add(m_And(m_Value(AndOp0), m_SpecificInt(Mask33)),
                        m_And(m_LShr(m_Deferred(AndOp0), m_SpecificInt(2)),
                              m_SpecificInt(Mask33))))) {
        Value *Root, *SubOp1;
        // Matching "i - ((i >> 1) & 0x55555555...)".
        if (match(AndOp0, m_Sub(m_Value(Root), m_Value(SubOp1))) &&
            match(SubOp1, m_And(m_LShr(m_Specific(Root), m_SpecificInt(1)),
                                m_SpecificInt(Mask55)))) {
          LLVM_DEBUG(dbgs() << "Recognized popcount intrinsic\n");
          IRBuilder<> Builder(&I);
          Function *Func = Intrinsic::getDeclaration(
              I.getModule(), Intrinsic::ctpop, I.getType());
          I.replaceAllUsesWith(Builder.CreateCall(Func, {Root}));
          ++NumPopCountRecognized;
          return true;
        }
      }
    }
  }

  return false;
}

/// Fold smin(smax(fptosi(x), C1), C2) to llvm.fptosi.sat(x), providing C1 and
/// C2 saturate the value of the fp conversion. The transform is not reversable
/// as the fptosi.sat is more defined than the input - all values produce a
/// valid value for the fptosi.sat, where as some produce poison for original
/// that were out of range of the integer conversion. The reversed pattern may
/// use fmax and fmin instead. As we cannot directly reverse the transform, and
/// it is not always profitable, we make it conditional on the cost being
/// reported as lower by TTI.
static bool tryToFPToSat(Instruction &I, TargetTransformInfo &TTI) {
  // Look for min(max(fptosi, converting to fptosi_sat.
  Value *In;
  const APInt *MinC, *MaxC;
  if (!match(&I, m_SMax(m_OneUse(m_SMin(m_OneUse(m_FPToSI(m_Value(In))),
                                        m_APInt(MinC))),
                        m_APInt(MaxC))) &&
      !match(&I, m_SMin(m_OneUse(m_SMax(m_OneUse(m_FPToSI(m_Value(In))),
                                        m_APInt(MaxC))),
                        m_APInt(MinC))))
    return false;

  // Check that the constants clamp a saturate.
  if (!(*MinC + 1).isPowerOf2() || -*MaxC != *MinC + 1)
    return false;

  Type *IntTy = I.getType();
  Type *FpTy = In->getType();
  Type *SatTy =
      IntegerType::get(IntTy->getContext(), (*MinC + 1).exactLogBase2() + 1);
  if (auto *VecTy = dyn_cast<VectorType>(IntTy))
    SatTy = VectorType::get(SatTy, VecTy->getElementCount());

  // Get the cost of the intrinsic, and check that against the cost of
  // fptosi+smin+smax
  InstructionCost SatCost = TTI.getIntrinsicInstrCost(
      IntrinsicCostAttributes(Intrinsic::fptosi_sat, SatTy, {In}, {FpTy}),
      TTI::TCK_RecipThroughput);
  SatCost += TTI.getCastInstrCost(Instruction::SExt, SatTy, IntTy,
                                  TTI::CastContextHint::None,
                                  TTI::TCK_RecipThroughput);

  InstructionCost MinMaxCost = TTI.getCastInstrCost(
      Instruction::FPToSI, IntTy, FpTy, TTI::CastContextHint::None,
      TTI::TCK_RecipThroughput);
  MinMaxCost += TTI.getIntrinsicInstrCost(
      IntrinsicCostAttributes(Intrinsic::smin, IntTy, {IntTy}),
      TTI::TCK_RecipThroughput);
  MinMaxCost += TTI.getIntrinsicInstrCost(
      IntrinsicCostAttributes(Intrinsic::smax, IntTy, {IntTy}),
      TTI::TCK_RecipThroughput);

  if (SatCost >= MinMaxCost)
    return false;

  IRBuilder<> Builder(&I);
  Function *Fn = Intrinsic::getDeclaration(I.getModule(), Intrinsic::fptosi_sat,
                                           {SatTy, FpTy});
  Value *Sat = Builder.CreateCall(Fn, In);
  I.replaceAllUsesWith(Builder.CreateSExt(Sat, IntTy));
  return true;
}

/// Try to replace a mathlib call to sqrt with the LLVM intrinsic. This avoids
/// pessimistic codegen that has to account for setting errno and can enable
/// vectorization.
static bool foldSqrt(Instruction &I, TargetTransformInfo &TTI,
                     TargetLibraryInfo &TLI) {
  // Match a call to sqrt mathlib function.
  auto *Call = dyn_cast<CallInst>(&I);
  if (!Call)
    return false;

  Module *M = Call->getModule();
  LibFunc Func;
  if (!TLI.getLibFunc(*Call, Func) || !isLibFuncEmittable(M, &TLI, Func))
    return false;

  if (Func != LibFunc_sqrt && Func != LibFunc_sqrtf && Func != LibFunc_sqrtl)
    return false;

  // If (1) this is a sqrt libcall, (2) we can assume that NAN is not created
  // (because NNAN or the operand arg must not be less than -0.0) and (2) we
  // would not end up lowering to a libcall anyway (which could change the value
  // of errno), then:
  // (1) errno won't be set.
  // (2) it is safe to convert this to an intrinsic call.
  Type *Ty = Call->getType();
  Value *Arg = Call->getArgOperand(0);
  if (TTI.haveFastSqrt(Ty) &&
      (Call->hasNoNaNs() ||
       CannotBeOrderedLessThanZero(Arg, M->getDataLayout(), &TLI))) {
    IRBuilder<> Builder(&I);
    IRBuilderBase::FastMathFlagGuard Guard(Builder);
    Builder.setFastMathFlags(Call->getFastMathFlags());

    Function *Sqrt = Intrinsic::getDeclaration(M, Intrinsic::sqrt, Ty);
    Value *NewSqrt = Builder.CreateCall(Sqrt, Arg, "sqrt");
    I.replaceAllUsesWith(NewSqrt);

    // Explicitly erase the old call because a call with side effects is not
    // trivially dead.
    I.eraseFromParent();
    return true;
  }

  return false;
}

//---------------------------------------------------------------------------------------------------------------------------------------
// Petar's code!
//LLVM IR code for the naive crc algorithm implementation!
/*
; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i16 @crcu8(i8 zeroext %0, i16 zeroext %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i16, align 2
  %5 = alloca i8, align 1
  %6 = alloca i8, align 1
  %7 = alloca i8, align 1
  store i8 %0, i8* %3, align 1
  store i16 %1, i16* %4, align 2
  store i8 0, i8* %5, align 1
  store i8 0, i8* %6, align 1
  store i8 0, i8* %7, align 1
  store i8 0, i8* %5, align 1
  br label %8

8:                                                ; preds = %53, %2
  %9 = load i8, i8* %5, align 1
  %10 = zext i8 %9 to i32
  %11 = icmp slt i32 %10, 8
  br i1 %11, label %12, label %56

12:                                               ; preds = %8
  %13 = load i8, i8* %3, align 1
  %14 = zext i8 %13 to i32
  %15 = and i32 %14, 1
  %16 = load i16, i16* %4, align 2
  %17 = trunc i16 %16 to i8
  %18 = zext i8 %17 to i32
  %19 = and i32 %18, 1
  %20 = xor i32 %15, %19
  %21 = trunc i32 %20 to i8
  store i8 %21, i8* %6, align 1
  %22 = load i8, i8* %3, align 1
  %23 = zext i8 %22 to i32
  %24 = ashr i32 %23, 1
  %25 = trunc i32 %24 to i8
  store i8 %25, i8* %3, align 1
  %26 = load i8, i8* %6, align 1
  %27 = zext i8 %26 to i32
  %28 = icmp eq i32 %27, 1
  br i1 %28, label %29, label %34

29:                                               ; preds = %12
  %30 = load i16, i16* %4, align 2
  %31 = zext i16 %30 to i32
  %32 = xor i32 %31, 16386
  %33 = trunc i32 %32 to i16
  store i16 %33, i16* %4, align 2
  store i8 1, i8* %7, align 1
  br label %35

34:                                               ; preds = %12
  store i8 0, i8* %7, align 1
  br label %35

35:                                               ; preds = %34, %29
  %36 = load i16, i16* %4, align 2
  %37 = zext i16 %36 to i32
  %38 = ashr i32 %37, 1
  %39 = trunc i32 %38 to i16
  store i16 %39, i16* %4, align 2
  %40 = load i8, i8* %7, align 1
  %41 = icmp ne i8 %40, 0
  br i1 %41, label %42, label %47

42:                                               ; preds = %35
  %43 = load i16, i16* %4, align 2
  %44 = zext i16 %43 to i32
  %45 = or i32 %44, 32768
  %46 = trunc i32 %45 to i16
  store i16 %46, i16* %4, align 2
  br label %52

47:                                               ; preds = %35
  %48 = load i16, i16* %4, align 2
  %49 = zext i16 %48 to i32
  %50 = and i32 %49, 32767
  %51 = trunc i32 %50 to i16
  store i16 %51, i16* %4, align 2
  br label %52

52:                                               ; preds = %47, %42
  br label %53

53:                                               ; preds = %52
  %54 = load i8, i8* %5, align 1
  %55 = add i8 %54, 1
  store i8 %55, i8* %5, align 1
  br label %8

56:                                               ; preds = %8
  %57 = load i16, i16* %4, align 2
  ret i16 %57
}
*/
static bool tryToRecognizeCRC32_v1(Instruction &I){
  ReturnInst *RI=dyn_cast<ReturnInst>(&I);
  ReturnInst *RIfinal=dyn_cast<ReturnInst>(&I);
  if(!RI || !RIfinal)
    return false;
  
  LoadInst *LI=dyn_cast<LoadInst>(RI->getPrevNode());
  LoadInst *LIfinal=dyn_cast<LoadInst>(RI->getPrevNode());
  if(!LI || !LIfinal)
    return false;
  
  errs() << "for.end: checked\n";

  BasicBlock *BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BranchInst *BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  StoreInst *SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  Instruction *II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!II)
    return false;

  Value *help1;
  Value *help2;
  if(!match(II, m_Add(m_Value(help1), m_Value(help2))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  errs() << "for.inc: checked\n";

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;  

  errs() << "if.end25: checked\n";

  BB=dyn_cast<BasicBlock>(BI->getParent()->getPrevNode());
  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  TruncInst *TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());  
  if(!match(II, m_And(m_Value(help1), m_SpecificInt(32767))))
    return false;

  ZExtInst *ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;


  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  errs() << "if.else21: checked\n";  

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;
 
  TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());
  // We should somehow recognize -32768 here!
  if(!match(II, m_Or(m_Value(help1), m_Value(help2))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  errs() << "if.then18: checked\n";

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICmpInst *ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  LI=dyn_cast<LoadInst>(ICMPI->getPrevNode());
  if(!LI)
    return false;
  
  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  errs() << "if.else: checked!\n";  

  BB=dyn_cast<BasicBlock>(SI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;                              
  
  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_Xor(m_Value(help1), m_SpecificInt(16386))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false; 

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  errs() << "if.then: checked!\n";

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  ZI=dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  SI=dyn_cast<StoreInst>(LI->getPrevNode());    
  if(!SI)
    return false;

  TI=dyn_cast<TruncInst>(SI->getPrevNode());    
  if(!TI)
    return false;          

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;    
  
  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_Xor(m_Value(help1), m_Value(help2))))
    return false;

  II=dyn_cast<Instruction>(II->getPrevNode());
  if(!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;    

  TI=dyn_cast<TruncInst>(ZI->getPrevNode());
  if(!TI)
    return false;    

  LI=dyn_cast<LoadInst>(TI->getPrevNode());
  if(!LI)
    return false;
  
  II=dyn_cast<Instruction>(LI->getPrevNode());
  if(!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  errs() << "for.body: checked!\n";

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  ZI=dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  errs() << "for.cond: checked!\n";

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;
  
  // Here we have to match 6 more consecutive store instructions and 5 consecutive alloca instructions!
  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;       

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false; 

  // Last thing we have to match are 5 alloca instructions!
  AllocaInst *AI=dyn_cast<AllocaInst>(SI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;                        
  
  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;    

  errs() << "Original unoptimized form of CRC32 algorithm has been recognized!\n";
  Value *argument1=LIfinal->getFunction()->getArg(0);
  Value *argument2=LIfinal->getFunction()->getArg(1);
  Type* ArgType1=argument1->getType();
  Type* ArgType2=argument2->getType();
  IRBuilder<> B(LIfinal);
  
  //Something to remember because it's very important!
  //Here is hidden a another aproach for replacing unoptimized crc with optimized version!
  //auto CRC8 = B.CreateIntrinsic(Intrinsic::crc8, {}, {argument1, argument2});
  auto CRC8 = B.CreateIntrinsic(Intrinsic::riscv_crc_petar, {}, {argument1, argument2});
  LIfinal->replaceAllUsesWith(CRC8);
  Function *F=LIfinal->getFunction();
  
  BasicBlock *bb_help10=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help9=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help8=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help7=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help6=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help5=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help4=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help3=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help2=RIfinal->getParent()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help1=RIfinal->getParent()->getPrevNode();
  DeleteDeadBlocks({bb_help1, bb_help2, bb_help3, bb_help4, bb_help5, bb_help6, bb_help7, bb_help8, bb_help9, bb_help10});
  
  F->back().back().getPrevNode()->eraseFromParent();

  //We will save this part of code! Just to have track of what we have created so far!
  errs() << "-----------------------------------------\n";
  errs() << F->getName() << ": \n";
  for(BasicBlock &BBIT: *F){
    for(Instruction &IIT: BBIT){
        errs() << IIT << "\n";
    }
  }
  errs() << "-----------------------------------------\n";

  return true;
}

static bool tryToRecognizeCRC32_v2(Instruction &I){
  ReturnInst *RI=dyn_cast<ReturnInst>(&I);
  ReturnInst *RIfinal=dyn_cast<ReturnInst>(&I);
  if(!RI || !RIfinal)
    return false;
  
  LoadInst *LI=dyn_cast<LoadInst>(RI->getPrevNode());
  LoadInst *LIfinal=dyn_cast<LoadInst>(RI->getPrevNode());
  if(!LI || !LIfinal)
    return false;

  BasicBlock *BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BranchInst *BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  StoreInst *SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  Instruction *II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!II)
    return false;

  Value *help1;
  Value *help2;
  II->dump();
  if(!match(II, m_Add(m_Load(m_Value(help1)), m_SpecificInt(1))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;  

  BB=dyn_cast<BasicBlock>(BI->getParent()->getPrevNode());
  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  // For some reason we could not see trunc instruction!
  II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!match(II, m_And(m_Load(m_Value(help1)), m_SpecificInt(32767))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  II=dyn_cast<Instruction>(SI->getPrevNode());
  II->dump();
  // We should somehow recognize -32768 here!
  if(!match(II, m_Or(m_Load(m_Value(help1)), m_Value(help2))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICmpInst *ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  LI=dyn_cast<LoadInst>(ICMPI->getPrevNode());
  if(!LI)
    return false;
  
  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  TruncInst *TI=dyn_cast<TruncInst>(SI->getPrevNode());
  if(!TI)
    return false;

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZExtInst *ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  BB=dyn_cast<BasicBlock>(SI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;                              
  
  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!match(II, m_Xor(m_Value(help1), m_SpecificInt(16386))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  ZI=dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  SI=dyn_cast<StoreInst>(LI->getPrevNode());    
  if(!SI)
    return false;

  TI=dyn_cast<TruncInst>(SI->getPrevNode());    
  if(!TI)
    return false;          

  II=dyn_cast<Instruction>(TI->getPrevNode());
  if(!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI=dyn_cast<ZExtInst>(II->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;    
  
  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!match(II, m_Xor(m_Value(help1), m_Value(help2))))
    return false;

  II=dyn_cast<Instruction>(II->getPrevNode());
  if(!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  TI=dyn_cast<TruncInst>(II->getPrevNode());
  if(!TI)
    return false;    

  LI=dyn_cast<LoadInst>(TI->getPrevNode());
  if(!LI)
    return false;
  
  II=dyn_cast<Instruction>(LI->getPrevNode());
  if(!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;

  ZI=dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if(!ZI)
    return false;

  LI=dyn_cast<LoadInst>(ZI->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if(!BB)
    return false;

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;
  
  // Here we have to match 6 more consecutive store instructions and 5 consecutive alloca instructions!
  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;       

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false; 

  // Last thing we have to match are 5 alloca instructions!
  AllocaInst *AI=dyn_cast<AllocaInst>(SI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;                        
  
  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;    

  errs() << "Original unoptimized form of CRC32 algorithm has been recognized!\n";
  Value *argument1=LIfinal->getFunction()->getArg(0);
  Value *argument2=LIfinal->getFunction()->getArg(1);
  Type* ArgType1=argument1->getType();
  Type* ArgType2=argument2->getType();
  IRBuilder<> B(LIfinal);
  
  BasicBlock *bb_help10=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help9=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help8=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help7=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help6=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help5=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help4=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help3=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help2=RIfinal->getParent()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help1=RIfinal->getParent()->getPrevNode();
  DeleteDeadBlocks({bb_help1, bb_help2, bb_help3, bb_help4, bb_help5, bb_help6, bb_help7, bb_help8, bb_help9, bb_help10});

  IRBuilder<> Builder(LIfinal);
  Function *F=LIfinal->getFunction();
  LIfinal->getParent()->setName("entry");
  AllocaInst *AI1=Builder.CreateAlloca(ArgType1, nullptr, "data.addr");
  AllocaInst *AI2=Builder.CreateAlloca(ArgType2, nullptr, "_crc.addr");
  AllocaInst *AI3=Builder.CreateAlloca(ArgType1, nullptr, "i");
  AllocaInst *AI4=Builder.CreateAlloca(ArgType1, nullptr, "x16");
  AllocaInst *AI5=Builder.CreateAlloca(ArgType1, nullptr, "carry");
  AllocaInst *AI6=Builder.CreateAlloca(Builder.getInt64Ty(), nullptr, "crc");
  StoreInst *SI1=Builder.CreateStore(argument1, AI1);
  StoreInst *SI2=Builder.CreateStore(argument2, AI2);
  StoreInst *SI3=Builder.CreateStore(Builder.getInt8(0), AI3);
  StoreInst *SI4=Builder.CreateStore(Builder.getInt8(0), AI4);  
  StoreInst *SI5=Builder.CreateStore(Builder.getInt8(0), AI5);
  LoadInst *LI1=Builder.CreateLoad(ArgType2, AI2, "");
  Value *ZI1=Builder.CreateZExt(LI1, Builder.getInt64Ty(), "conv");
  StoreInst *SI6=Builder.CreateStore(ZI1, AI6);
  LoadInst *LI2=Builder.CreateLoad(Builder.getInt8Ty(), AI1, "");
  Value *ZI2=Builder.CreateZExt(LI2, Builder.getInt64Ty(), "conv1");
  LoadInst *LI3=Builder.CreateLoad(Builder.getInt64Ty(), AI6, "");
  Value *XOR1=Builder.CreateXor(LI3, ZI2, "xor");
  StoreInst *SI7=Builder.CreateStore(XOR1, AI6);
  StoreInst *SI8=Builder.CreateStore(Builder.getInt8(0), AI3);
  
  BasicBlock* ForEndBB = BasicBlock::Create(F->getContext(), "for.end", F, nullptr);
  Instruction *I1=LIfinal;
  Instruction *I2=LIfinal->getNextNode(); 
  I1->removeFromParent();
  I2->removeFromParent();
  I1->insertInto(ForEndBB, ForEndBB->end());
  I2->insertInto(ForEndBB, ForEndBB->end());

  //IRBuilder<> Builder1(SI8->getParent(), SI8->getParent()->end());
  //BranchInst *BI1=Builder1.CreateBr(ForCondBB);

  //I think we can start this way!
  BasicBlock* ForCondBB = BasicBlock::Create(F->getContext(), "for.cond", F, ForEndBB);
  IRBuilder<> ForCondBuilder(ForCondBB, ForCondBB->end()); 
  BasicBlock* ForBodyBB = BasicBlock::Create(F->getContext(), "for.body", F, ForEndBB);
  IRBuilder<> ForBodyBuilder(ForBodyBB, ForBodyBB->end());
  BasicBlock* ForIncBB = BasicBlock::Create(F->getContext(), "for.inc", F, ForEndBB);
  IRBuilder<> ForIncBuilder(ForIncBB, ForIncBB->end());  

  IRBuilder<> Builder1(SI8->getParent(), SI8->getParent()->end());
  BranchInst *BI1=Builder1.CreateBr(ForCondBB);

  //Everything is okay with creation of "for.cond" basic block! 
  LoadInst *LI4=ForCondBuilder.CreateLoad(ForCondBuilder.getInt8Ty(), AI6);
  Value *ZI3=ForCondBuilder.CreateZExt(LI4, ForCondBuilder.getInt32Ty(), "conv2");
  Value *ICI1=ForCondBuilder.CreateICmp(llvm::CmpInst::ICMP_SLT, ZI3, ForCondBuilder.getInt32(8), "cmp");
  BranchInst *BI2=ForCondBuilder.CreateCondBr(ICI1, ForBodyBB, ForEndBB);
  
  //Everything is okay with creation of "for.body" basic block! 
  LoadInst *LI5=ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *TI1=ForBodyBuilder.CreateTrunc(LI5, ForBodyBuilder.getInt8Ty(), "conv4");
  Value *ZI4=ForBodyBuilder.CreateZExt(TI1, ForCondBuilder.getInt32Ty(), "conv5");
  Value *And1=ForBodyBuilder.CreateAnd(ZI4, ForBodyBuilder.getInt32(1), "and");
  Value *TI2=ForBodyBuilder.CreateTrunc(And1, ForBodyBuilder.getInt8Ty(), "conv6");
  StoreInst *SI9=ForBodyBuilder.CreateStore(TI2, AI4);
  LoadInst *LI6=ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI1);
  Value *ZI5=ForBodyBuilder.CreateZExt(LI6, ForCondBuilder.getInt32Ty(), "conv7");
  Value *Ashr1=ForBodyBuilder.CreateAShr(ZI5, ForBodyBuilder.getInt32(1), "shr");
  Value *TI3=ForBodyBuilder.CreateTrunc(Ashr1, ForBodyBuilder.getInt8Ty(), "conv8");
  StoreInst *SI10=ForBodyBuilder.CreateStore(TI3, AI1);
  LoadInst *LI7=ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *Ashr2=ForBodyBuilder.CreateAShr(LI7, ForBodyBuilder.getInt64(1), "shr9");
  StoreInst *SI11=ForBodyBuilder.CreateStore(Ashr2, AI6);
  LoadInst *LI8=ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI4);
  Value *ZI6=ForBodyBuilder.CreateZExt(LI8, ForCondBuilder.getInt32Ty(), "conv10");
  Value *And2=ForBodyBuilder.CreateAnd(ZI6, ForBodyBuilder.getInt32(1), "and11");
  Value *ICI2=ForBodyBuilder.CreateICmp(llvm::CmpInst::ICMP_NE, And2, ForCondBuilder.getInt32(0), "tobool");
  Value *ZI7=ForBodyBuilder.CreateZExt(ICI2, ForCondBuilder.getInt64Ty(), "");
  Value *Select1=ForBodyBuilder.CreateSelect(ICI2, ForBodyBuilder.getInt32(40961), ForBodyBuilder.getInt32(0));
  Value *Sext1=ForBodyBuilder.CreateSExt(Select1, ForBodyBuilder.getInt64Ty(), "conv12");
  LoadInst *LI9=ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *XOR2=ForBodyBuilder.CreateXor(LI9, Sext1, "xor13");
  StoreInst *SI12=ForBodyBuilder.CreateStore(XOR2, AI6);
  BranchInst *BI3=ForBodyBuilder.CreateBr(ForIncBB);

  //Everything is okay with creation of "for.inc" basic block!
  LoadInst *LI10=ForIncBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI3);
  Value *Add1=ForIncBuilder.CreateAdd(LI10, ForIncBuilder.getInt8(1), "inc");
  StoreInst *SI20=ForIncBuilder.CreateStore(Add1, AI3);
  //We need to check this branch instruction again!
  BranchInst *BI4=ForIncBuilder.CreateBr(ForCondBB);

  //Last, we have to change a couple of instructions within "for.end" basic block!
  IRBuilder<> ForEndBuilder(LIfinal);
  LoadInst *LI11=ForEndBuilder.CreateLoad(B.getInt64Ty(), AI6);
  Value* TI20=ForEndBuilder.CreateTrunc(LI11, B.getInt16Ty(), "conv14");

  LIfinal->replaceAllUsesWith(TI20);
  
  F->back().back().getPrevNode()->eraseFromParent();
  //We will save this part of code! Just to have track of what we have created so far!
  
  errs() << "-----------------------------------------\n";
  errs() << "Function name: " << F->getName() << " \n";
  errs() << "Function body:\n";
  for(BasicBlock &BBIT: *F){
    errs() << BBIT.getName() << ":\n";
    for(Instruction &IIT: BBIT){
        errs() << IIT << "\n";
    }
  }
  errs() << "-----------------------------------------\n";

  return true;
}

// Check if this array of constants represents a crc32 table.
static bool isCRC32Table(const ConstantDataArray &Table){
  unsigned Length=Table.getNumElements();
  if(Length!=256)
    return false;
   
  for(int i=0;i<Length;i++){
    uint64_t Element=Table.getElementAsInteger(i);
    if(Element<0 || Element>4294967295)
      return false;
  }

  return true;  
} 

// Try to recognize table-based crc32 algorithm implementation.
/*
define internal i32 @singletable_crc32c(i32 %0, i8* %1, i64 %2) #0 {
  %4 = alloca i32, align 4
  %5 = alloca i8*, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32*, align 8
  store i32 %0, i32* %4, align 4
  store i8* %1, i8** %5, align 8
  store i64 %2, i64* %6, align 8
  %8 = load i8*, i8** %5, align 8
  %9 = bitcast i8* %8 to i32*
  store i32* %9, i32** %7, align 8
  br label %10

10:                                               ; preds = %14, %3
  %11 = load i64, i64* %6, align 8
  %12 = add i64 %11, -1
  store i64 %12, i64* %6, align 8
  %13 = icmp ne i64 %11, 0
  br i1 %13, label %14, label %27

14:                                               ; preds = %10
  %15 = load i32, i32* %4, align 4
  %16 = load i32*, i32** %7, align 8
  %17 = getelementptr inbounds i32, i32* %16, i32 1
  store i32* %17, i32** %7, align 8
  %18 = load i32, i32* %16, align 4
  %19 = xor i32 %15, %18
  %20 = and i32 %19, 255
  %21 = zext i32 %20 to i64
  %22 = getelementptr inbounds [256 x i32], [256 x i32]* @crc32Table, i64 0, i64 %21
  %23 = load i32, i32* %22, align 4
  %24 = load i32, i32* %4, align 4
  %25 = lshr i32 %24, 8
  %26 = xor i32 %23, %25
  store i32 %26, i32* %4, align 4
  br label %10

27:                                               ; preds = %10
  %28 = load i32, i32* %4, align 4
  ret i32 %28
}
*/
static bool tryToRecognizeTableBasedCRC32(Instruction &I){
  ReturnInst *RI=dyn_cast<ReturnInst>(&I);
  ReturnInst *RIfinal=dyn_cast<ReturnInst>(&I);
  if(!RI)
    return false;
  
  LoadInst *LI = dyn_cast<LoadInst>(RI->getPrevNode());
  if (!LI)
    return false;
  
  LoadInst *LIfinal=dyn_cast<LoadInst>(LI);
  Type *AccessType = LI->getType(); 
  if (!AccessType->isIntegerTy())
    return false; 
  
  BasicBlock *BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  
  BranchInst *BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  StoreInst *SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;

  Instruction *II=dyn_cast<Instruction>(SI->getPrevNode());
  Value *help1;
  Value *help2;
  if(!match(II, m_Xor(m_Value(help1), m_Value(help2))))
    return false;

  II=dyn_cast<Instruction>(II->getPrevNode());
  
  if(!match(II, m_LShr(m_Value(help1), m_SpecificInt(8))))
    return false;     
  
  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  LI=dyn_cast<LoadInst>(LI->getPrevNode());
  if(!LI)
    return false;
  
  // Temporary insertion!!!!!!!!!!!!!
  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(LI->getPointerOperand());
  if (!GEP || !GEP->isInBounds() || GEP->getNumIndices() != 2)
    return false;

  GlobalVariable *GVTable = dyn_cast<GlobalVariable>(GEP->getPointerOperand());
  if (!GVTable || !GVTable->hasInitializer() || !GVTable->isConstant())
    return false;

  ConstantDataArray *ConstData=dyn_cast<ConstantDataArray>(GVTable->getInitializer());
  if (!ConstData)
    return false;
  
  if (!isCRC32Table(*ConstData))
    return false;
  // End of temporary insertion!!!!!!!!!!!!! 
   
  
  GetElementPtrInst *GEPI=dyn_cast<GetElementPtrInst>(LI->getPrevNode());
  if(!GEPI)
    return false;

  ZExtInst *ZI=dyn_cast<ZExtInst>(GEPI->getPrevNode());
  if(!ZI)
    return false;

  II=dyn_cast<Instruction>(ZI->getPrevNode());
  if(!match(II, m_And(m_Value(help1), m_Value(help2))))
    return false;
  
  Value *X1;

  II=dyn_cast<Instruction>(II->getPrevNode());
  if(!match(II, m_Xor(m_Value(X1), m_Value(help2))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;  

  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  GEPI=dyn_cast<GetElementPtrInst>(SI->getPrevNode());
  if(!GEPI)
    return false; 

  LI=dyn_cast<LoadInst>(GEPI->getPrevNode());
  if(!LI)
    return false;
  
  LI=dyn_cast<LoadInst>(LI->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;  

  ICmpInst *ICMPI=dyn_cast<ICmpInst>(BI->getPrevNode());
  if(!ICMPI)
    return false;
  
  SI=dyn_cast<StoreInst>(ICMPI->getPrevNode());
  if(!SI)
    return false;

  II=dyn_cast<Instruction>(SI->getPrevNode());
  if(!match(II, m_Add(m_Value(help1), m_SpecificInt(-1))))
    return false;

  LI=dyn_cast<LoadInst>(II->getPrevNode());
  if(!LI)
    return false;

  BB=dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());

  BI=dyn_cast<BranchInst>(&BB->back());
  if(!BI)
    return false;

  SI=dyn_cast<StoreInst>(BI->getPrevNode());
  if(!SI)
    return false;
  
  BitCastInst *BCI=dyn_cast<BitCastInst>(SI->getPrevNode());
  if(!BCI)
    return false;

  LI=dyn_cast<LoadInst>(BCI->getPrevNode());
  if(!LI)
    return false;

  SI=dyn_cast<StoreInst>(LI->getPrevNode());
  if(!SI)
    return false;

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false;      

  SI=dyn_cast<StoreInst>(SI->getPrevNode());
  if(!SI)
    return false; 

  AllocaInst *AI=dyn_cast<AllocaInst>(SI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  AI=dyn_cast<AllocaInst>(AI->getPrevNode());
  if(!AI)
    return false;

  
  errs() << "!!!Table-based CRC32 algorithm is finally recognized!!!" << "\n";
  errs() << "It will be nice if we can check the value of the operands in this algorithm implementation!" << "\n";

  //We land this from tryToRecognizeTableBasedCTTZ function!
  auto ZeroTableElem = ConstData->getElementAsInteger(0);
  unsigned InputBits = X1->getType()->getScalarSizeInBits();
  bool DefinedForZero = ZeroTableElem == InputBits;
  
  IRBuilder<> B(LIfinal);
  ConstantInt *BoolConst = B.getInt1(!DefinedForZero);
  Type *XType = X1->getType();
  Value *final_arg=LIfinal->getFunction()->getArg(0);
  auto CRC = B.CreateIntrinsic(Intrinsic::crc, {XType}, {final_arg, BoolConst});
  Value *ZExtOrTrunc = nullptr;
  //New insertion for crc32 intrinsic!
  Value *argument1=LIfinal->getFunction()->getArg(0);
  Value *argument2=LIfinal->getFunction()->getArg(1);
  Value *argument3=LIfinal->getFunction()->getArg(2);
  //auto CRC32 = B.CreateIntrinsic(Intrinsic::crc32, {XType}, {argument1, argument2, argument3});
  //End of new insertion!
  
  errs() << final_arg->getType()->isIntOrIntVectorTy() << "\n";
  errs() << XType->isIntOrIntVectorTy() << "\n";
  errs()<< CRC->getType()->isIntOrIntVectorTy() << "\n";
  errs() << AccessType->isIntOrIntVectorTy() << "\n";

  //RIfinal->dump();
  //LIfinal->dump();
  //X1->dump();

  LIfinal->replaceAllUsesWith(CRC);
  //LIfinal->replaceAllUsesWith(CRC32);

  BasicBlock *bb_help1=RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help2=RIfinal->getParent()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help3=RIfinal->getParent()->getPrevNode();
  DeleteDeadBlocks({bb_help3, bb_help2, bb_help1});
  errs() << "We did it?!" << "\n";

  Function *f=dyn_cast<Function>(LIfinal->getParent()->getParent());
  Module *m=f->getParent();
  auto call_function=m->getFunction("llvm.crc.i32");
  if(call_function!=NULL){
    errs() << "Wow!" << "\n";
  } else {
    errs() << "Failed!" << "\n";
  }

  return true;
}

// Check if this array of constants represents a cttz table.
// Iterate over the elements from \p Table by trying to find/match all
// the numbers from 0 to \p InputBits that should represent cttz results.
static bool isCTTZTable(const ConstantDataArray &Table, uint64_t Mul,
                        uint64_t Shift, uint64_t InputBits) {
  unsigned Length = Table.getNumElements();
  if (Length < InputBits || Length > InputBits * 2)
    return false;

  APInt Mask = APInt::getBitsSetFrom(InputBits, Shift);
  unsigned Matched = 0;

  for (unsigned i = 0; i < Length; i++) {
    uint64_t Element = Table.getElementAsInteger(i);
    if (Element >= InputBits)
      continue;

    // Check if \p Element matches a concrete answer. It could fail for some
    // elements that are never accessed, so we keep iterating over each element
    // from the table. The number of matched elements should be equal to the
    // number of potential right answers which is \p InputBits actually.
    if ((((Mul << Element) & Mask.getZExtValue()) >> Shift) == i)
      Matched++;
  }

  return Matched == InputBits;
}

// Try to recognize table-based ctz implementation.
// E.g., an example in C (for more cases please see the llvm/tests):
// int f(unsigned x) {
//    static const char table[32] =
//      {0, 1, 28, 2, 29, 14, 24, 3, 30,
//        22, 20, 15, 25, 17, 4, 8, 31, 27,
//       13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9};
//    return table[((unsigned)((x & -x) * 0x077CB531U)) >> 27];
// }
// this can be lowered to `cttz` instruction.
// There is also a special case when the element is 0.
//
// Here are some examples or LLVM IR for a 64-bit target:
//
// CASE 1:
// %sub = sub i32 0, %x
// %and = and i32 %sub, %x
// %mul = mul i32 %and, 125613361
// %shr = lshr i32 %mul, 27
// %idxprom = zext i32 %shr to i64
// %arrayidx = getelementptr inbounds [32 x i8], [32 x i8]* @ctz1.table, i64 0,
// i64 %idxprom %0 = load i8, i8* %arrayidx, align 1, !tbaa !8
//
// CASE 2:
// %sub = sub i32 0, %x
// %and = and i32 %sub, %x
// %mul = mul i32 %and, 72416175
// %shr = lshr i32 %mul, 26
// %idxprom = zext i32 %shr to i64
// %arrayidx = getelementptr inbounds [64 x i16], [64 x i16]* @ctz2.table, i64
// 0, i64 %idxprom %0 = load i16, i16* %arrayidx, align 2, !tbaa !8
//
// CASE 3:
// %sub = sub i32 0, %x
// %and = and i32 %sub, %x
// %mul = mul i32 %and, 81224991
// %shr = lshr i32 %mul, 27
// %idxprom = zext i32 %shr to i64
// %arrayidx = getelementptr inbounds [32 x i32], [32 x i32]* @ctz3.table, i64
// 0, i64 %idxprom %0 = load i32, i32* %arrayidx, align 4, !tbaa !8
//
// CASE 4:
// %sub = sub i64 0, %x
// %and = and i64 %sub, %x
// %mul = mul i64 %and, 283881067100198605
// %shr = lshr i64 %mul, 58
// %arrayidx = getelementptr inbounds [64 x i8], [64 x i8]* @table, i64 0, i64
// %shr %0 = load i8, i8* %arrayidx, align 1, !tbaa !8
//
// All this can be lowered to @llvm.cttz.i32/64 intrinsic.
static bool tryToRecognizeTableBasedCttz(Instruction &I) {
  LoadInst *LI = dyn_cast<LoadInst>(&I);
  if (!LI)
    return false;

  Type *AccessType = LI->getType();
  if (!AccessType->isIntegerTy())
    return false;

  GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(LI->getPointerOperand());
  if (!GEP || !GEP->isInBounds() || GEP->getNumIndices() != 2)
    return false;

  if (!GEP->getSourceElementType()->isArrayTy())
    return false;

  uint64_t ArraySize = GEP->getSourceElementType()->getArrayNumElements();
  if (ArraySize != 32 && ArraySize != 64)
    return false;

  GlobalVariable *GVTable = dyn_cast<GlobalVariable>(GEP->getPointerOperand());
  if (!GVTable || !GVTable->hasInitializer() || !GVTable->isConstant())
    return false;

  ConstantDataArray *ConstData =
      dyn_cast<ConstantDataArray>(GVTable->getInitializer());
  if (!ConstData)
    return false;

  if (!match(GEP->idx_begin()->get(), m_ZeroInt()))
    return false;

  Value *Idx2 = std::next(GEP->idx_begin())->get();
  Value *X1;
  uint64_t MulConst, ShiftConst;
  // FIXME: 64-bit targets have `i64` type for the GEP index, so this match will
  // probably fail for other (e.g. 32-bit) targets.
  if (!match(Idx2, m_ZExtOrSelf(
                       m_LShr(m_Mul(m_c_And(m_Neg(m_Value(X1)), m_Deferred(X1)),
                                    m_ConstantInt(MulConst)),
                              m_ConstantInt(ShiftConst)))))
    return false;
  // %sub = sub i32 0, %x
  // %and = and i32 %sub, %x
  // %mul = mul i32 %and, 81224991
  // %shr = lshr i32 %mul, 27
  // %idxprom = zext i32 %shr to i64
  unsigned InputBits = X1->getType()->getScalarSizeInBits();
  if (InputBits != 32 && InputBits != 64)
    return false;

  // Shift should extract top 5..7 bits.
  if (InputBits - Log2_32(InputBits) != ShiftConst &&
      InputBits - Log2_32(InputBits) - 1 != ShiftConst)
    return false;

  if (!isCTTZTable(*ConstData, MulConst, ShiftConst, InputBits))
    return false;

  auto ZeroTableElem = ConstData->getElementAsInteger(0);
  bool DefinedForZero = ZeroTableElem == InputBits;

  IRBuilder<> B(LI);
  ConstantInt *BoolConst = B.getInt1(!DefinedForZero);
  Type *XType = X1->getType();
  auto Cttz = B.CreateIntrinsic(Intrinsic::cttz, {XType}, {X1, BoolConst});
  
  errs() << "Table-based cttz algorithm is recognized!" << "\n";
  errs()<< Cttz->getType()->isIntOrIntVectorTy() << "\n";

  Value *ZExtOrTrunc = nullptr;

  if (DefinedForZero) {
    ZExtOrTrunc = B.CreateZExtOrTrunc(Cttz, AccessType);
  } else {
    // If the value in elem 0 isn't the same as InputBits, we still want to
    // produce the value from the table.
    auto Cmp = B.CreateICmpEQ(X1, ConstantInt::get(XType, 0));
    auto Select =
        B.CreateSelect(Cmp, ConstantInt::get(XType, ZeroTableElem), Cttz);

    // NOTE: If the table[0] is 0, but the cttz(0) is defined by the Target
    // it should be handled as: `cttz(x) & (typeSize - 1)`.

    ZExtOrTrunc = B.CreateZExtOrTrunc(Select, AccessType);
  }

  LI->replaceAllUsesWith(ZExtOrTrunc);

  return true;
}

/// This is used by foldLoadsRecursive() to capture a Root Load node which is
/// of type or(load, load) and recursively build the wide load. Also capture the
/// shift amount, zero extend type and loadSize.
struct LoadOps {
  LoadInst *Root = nullptr;
  LoadInst *RootInsert = nullptr;
  bool FoundRoot = false;
  uint64_t LoadSize = 0;
  const APInt *Shift = nullptr;
  Type *ZextType;
  AAMDNodes AATags;
};

// Identify and Merge consecutive loads recursively which is of the form
// (ZExt(L1) << shift1) | (ZExt(L2) << shift2) -> ZExt(L3) << shift1
// (ZExt(L1) << shift1) | ZExt(L2) -> ZExt(L3)
static bool foldLoadsRecursive(Value *V, LoadOps &LOps, const DataLayout &DL,
                               AliasAnalysis &AA) {
  const APInt *ShAmt2 = nullptr;
  Value *X;
  Instruction *L1, *L2;

  // Go to the last node with loads.
  if (match(V, m_OneUse(m_c_Or(
                   m_Value(X),
                   m_OneUse(m_Shl(m_OneUse(m_ZExt(m_OneUse(m_Instruction(L2)))),
                                  m_APInt(ShAmt2)))))) ||
      match(V, m_OneUse(m_Or(m_Value(X),
                             m_OneUse(m_ZExt(m_OneUse(m_Instruction(L2)))))))) {
    if (!foldLoadsRecursive(X, LOps, DL, AA) && LOps.FoundRoot)
      // Avoid Partial chain merge.
      return false;
  } else
    return false;

  // Check if the pattern has loads
  LoadInst *LI1 = LOps.Root;
  const APInt *ShAmt1 = LOps.Shift;
  if (LOps.FoundRoot == false &&
      (match(X, m_OneUse(m_ZExt(m_Instruction(L1)))) ||
       match(X, m_OneUse(m_Shl(m_OneUse(m_ZExt(m_OneUse(m_Instruction(L1)))),
                               m_APInt(ShAmt1)))))) {
    LI1 = dyn_cast<LoadInst>(L1);
  }
  LoadInst *LI2 = dyn_cast<LoadInst>(L2);

  // Check if loads are same, atomic, volatile and having same address space.
  if (LI1 == LI2 || !LI1 || !LI2 || !LI1->isSimple() || !LI2->isSimple() ||
      LI1->getPointerAddressSpace() != LI2->getPointerAddressSpace())
    return false;

  // Check if Loads come from same BB.
  if (LI1->getParent() != LI2->getParent())
    return false;

  // Find the data layout
  bool IsBigEndian = DL.isBigEndian();

  // Check if loads are consecutive and same size.
  Value *Load1Ptr = LI1->getPointerOperand();
  APInt Offset1(DL.getIndexTypeSizeInBits(Load1Ptr->getType()), 0);
  Load1Ptr =
      Load1Ptr->stripAndAccumulateConstantOffsets(DL, Offset1,
                                                  /* AllowNonInbounds */ true);

  Value *Load2Ptr = LI2->getPointerOperand();
  APInt Offset2(DL.getIndexTypeSizeInBits(Load2Ptr->getType()), 0);
  Load2Ptr =
      Load2Ptr->stripAndAccumulateConstantOffsets(DL, Offset2,
                                                  /* AllowNonInbounds */ true);

  // Verify if both loads have same base pointers and load sizes are same.
  uint64_t LoadSize1 = LI1->getType()->getPrimitiveSizeInBits();
  uint64_t LoadSize2 = LI2->getType()->getPrimitiveSizeInBits();
  if (Load1Ptr != Load2Ptr || LoadSize1 != LoadSize2)
    return false;

  // Support Loadsizes greater or equal to 8bits and only power of 2.
  if (LoadSize1 < 8 || !isPowerOf2_64(LoadSize1))
    return false;

  // Alias Analysis to check for stores b/w the loads.
  LoadInst *Start = LOps.FoundRoot ? LOps.RootInsert : LI1, *End = LI2;
  MemoryLocation Loc;
  if (!Start->comesBefore(End)) {
    std::swap(Start, End);
    Loc = MemoryLocation::get(End);
    if (LOps.FoundRoot)
      Loc = Loc.getWithNewSize(LOps.LoadSize);
  } else
    Loc = MemoryLocation::get(End);
  unsigned NumScanned = 0;
  for (Instruction &Inst :
       make_range(Start->getIterator(), End->getIterator())) {
    if (Inst.mayWriteToMemory() && isModSet(AA.getModRefInfo(&Inst, Loc)))
      return false;
    if (++NumScanned > MaxInstrsToScan)
      return false;
  }

  // Make sure Load with lower Offset is at LI1
  bool Reverse = false;
  if (Offset2.slt(Offset1)) {
    std::swap(LI1, LI2);
    std::swap(ShAmt1, ShAmt2);
    std::swap(Offset1, Offset2);
    std::swap(Load1Ptr, Load2Ptr);
    std::swap(LoadSize1, LoadSize2);
    Reverse = true;
  }

  // Big endian swap the shifts
  if (IsBigEndian)
    std::swap(ShAmt1, ShAmt2);

  // Find Shifts values.
  uint64_t Shift1 = 0, Shift2 = 0;
  if (ShAmt1)
    Shift1 = ShAmt1->getZExtValue();
  if (ShAmt2)
    Shift2 = ShAmt2->getZExtValue();

  // First load is always LI1. This is where we put the new load.
  // Use the merged load size available from LI1 for forward loads.
  if (LOps.FoundRoot) {
    if (!Reverse)
      LoadSize1 = LOps.LoadSize;
    else
      LoadSize2 = LOps.LoadSize;
  }

  // Verify if shift amount and load index aligns and verifies that loads
  // are consecutive.
  uint64_t ShiftDiff = IsBigEndian ? LoadSize2 : LoadSize1;
  uint64_t PrevSize =
      DL.getTypeStoreSize(IntegerType::get(LI1->getContext(), LoadSize1));
  if ((Shift2 - Shift1) != ShiftDiff || (Offset2 - Offset1) != PrevSize)
    return false;

  // Update LOps
  AAMDNodes AATags1 = LOps.AATags;
  AAMDNodes AATags2 = LI2->getAAMetadata();
  if (LOps.FoundRoot == false) {
    LOps.FoundRoot = true;
    AATags1 = LI1->getAAMetadata();
  }
  LOps.LoadSize = LoadSize1 + LoadSize2;
  LOps.RootInsert = Start;

  // Concatenate the AATags of the Merged Loads.
  LOps.AATags = AATags1.concat(AATags2);

  LOps.Root = LI1;
  LOps.Shift = ShAmt1;
  LOps.ZextType = X->getType();
  return true;
}

// For a given BB instruction, evaluate all loads in the chain that form a
// pattern which suggests that the loads can be combined. The one and only use
// of the loads is to form a wider load.
static bool foldConsecutiveLoads(Instruction &I, const DataLayout &DL,
                                 TargetTransformInfo &TTI, AliasAnalysis &AA,
                                 const DominatorTree &DT) {
  // Only consider load chains of scalar values.
  if (isa<VectorType>(I.getType()))
    return false;

  LoadOps LOps;
  if (!foldLoadsRecursive(&I, LOps, DL, AA) || !LOps.FoundRoot)
    return false;

  IRBuilder<> Builder(&I);
  LoadInst *NewLoad = nullptr, *LI1 = LOps.Root;

  IntegerType *WiderType = IntegerType::get(I.getContext(), LOps.LoadSize);
  // TTI based checks if we want to proceed with wider load
  bool Allowed = TTI.isTypeLegal(WiderType);
  if (!Allowed)
    return false;

  unsigned AS = LI1->getPointerAddressSpace();
  unsigned Fast = 0;
  Allowed = TTI.allowsMisalignedMemoryAccesses(I.getContext(), LOps.LoadSize,
                                               AS, LI1->getAlign(), &Fast);
  if (!Allowed || !Fast)
    return false;

  // Get the Index and Ptr for the new GEP.
  Value *Load1Ptr = LI1->getPointerOperand();
  Builder.SetInsertPoint(LOps.RootInsert);
  if (!DT.dominates(Load1Ptr, LOps.RootInsert)) {
    APInt Offset1(DL.getIndexTypeSizeInBits(Load1Ptr->getType()), 0);
    Load1Ptr = Load1Ptr->stripAndAccumulateConstantOffsets(
        DL, Offset1, /* AllowNonInbounds */ true);
    Load1Ptr = Builder.CreateGEP(Builder.getInt8Ty(), Load1Ptr,
                                 Builder.getInt32(Offset1.getZExtValue()));
  }
  // Generate wider load.
  Value *NewPtr = Builder.CreateBitCast(Load1Ptr, WiderType->getPointerTo(AS));
  NewLoad = Builder.CreateAlignedLoad(WiderType, NewPtr, LI1->getAlign(),
                                      LI1->isVolatile(), "");
  NewLoad->takeName(LI1);
  // Set the New Load AATags Metadata.
  if (LOps.AATags)
    NewLoad->setAAMetadata(LOps.AATags);

  Value *NewOp = NewLoad;
  // Check if zero extend needed.
  if (LOps.ZextType)
    NewOp = Builder.CreateZExt(NewOp, LOps.ZextType);

  // Check if shift needed. We need to shift with the amount of load1
  // shift if not zero.
  if (LOps.Shift)
    NewOp = Builder.CreateShl(NewOp, ConstantInt::get(I.getContext(), *LOps.Shift));
  I.replaceAllUsesWith(NewOp);

  return true;
}

// Calculate GEP Stride and accumulated const ModOffset. Return Stride and
// ModOffset
static std::pair<APInt, APInt>
getStrideAndModOffsetOfGEP(Value *PtrOp, const DataLayout &DL) {
  unsigned BW = DL.getIndexTypeSizeInBits(PtrOp->getType());
  std::optional<APInt> Stride;
  APInt ModOffset(BW, 0);
  // Return a minimum gep stride, greatest common divisor of consective gep
  // index scales(c.f. Bézout's identity).
  while (auto *GEP = dyn_cast<GEPOperator>(PtrOp)) {
    MapVector<Value *, APInt> VarOffsets;
    if (!GEP->collectOffset(DL, BW, VarOffsets, ModOffset))
      break;

    for (auto [V, Scale] : VarOffsets) {
      // Only keep a power of two factor for non-inbounds
      if (!GEP->isInBounds())
        Scale = APInt::getOneBitSet(Scale.getBitWidth(), Scale.countr_zero());

      if (!Stride)
        Stride = Scale;
      else
        Stride = APIntOps::GreatestCommonDivisor(*Stride, Scale);
    }

    PtrOp = GEP->getPointerOperand();
  }

  // Check whether pointer arrives back at Global Variable via at least one GEP.
  // Even if it doesn't, we can check by alignment.
  if (!isa<GlobalVariable>(PtrOp) || !Stride)
    return {APInt(BW, 1), APInt(BW, 0)};

  // In consideration of signed GEP indices, non-negligible offset become
  // remainder of division by minimum GEP stride.
  ModOffset = ModOffset.srem(*Stride);
  if (ModOffset.isNegative())
    ModOffset += *Stride;

  return {*Stride, ModOffset};
}

/// If C is a constant patterned array and all valid loaded results for given
/// alignment are same to a constant, return that constant.
static bool foldPatternedLoads(Instruction &I, const DataLayout &DL) {
  auto *LI = dyn_cast<LoadInst>(&I);
  if (!LI || LI->isVolatile())
    return false;

  // We can only fold the load if it is from a constant global with definitive
  // initializer. Skip expensive logic if this is not the case.
  auto *PtrOp = LI->getPointerOperand();
  auto *GV = dyn_cast<GlobalVariable>(getUnderlyingObject(PtrOp));
  if (!GV || !GV->isConstant() || !GV->hasDefinitiveInitializer())
    return false;

  // Bail for large initializers in excess of 4K to avoid too many scans.
  Constant *C = GV->getInitializer();
  uint64_t GVSize = DL.getTypeAllocSize(C->getType());
  if (!GVSize || 4096 < GVSize)
    return false;

  Type *LoadTy = LI->getType();
  unsigned BW = DL.getIndexTypeSizeInBits(PtrOp->getType());
  auto [Stride, ConstOffset] = getStrideAndModOffsetOfGEP(PtrOp, DL);

  // Any possible offset could be multiple of GEP stride. And any valid
  // offset is multiple of load alignment, so checking only multiples of bigger
  // one is sufficient to say results' equality.
  if (auto LA = LI->getAlign();
      LA <= GV->getAlign().valueOrOne() && Stride.getZExtValue() < LA.value()) {
    ConstOffset = APInt(BW, 0);
    Stride = APInt(BW, LA.value());
  }

  Constant *Ca = ConstantFoldLoadFromConst(C, LoadTy, ConstOffset, DL);
  if (!Ca)
    return false;

  unsigned E = GVSize - DL.getTypeStoreSize(LoadTy);
  for (; ConstOffset.getZExtValue() <= E; ConstOffset += Stride)
    if (Ca != ConstantFoldLoadFromConst(C, LoadTy, ConstOffset, DL))
      return false;

  I.replaceAllUsesWith(Ca);

  return true;
}

/// This is the entry point for folds that could be implemented in regular
/// InstCombine, but they are separated because they are not expected to
/// occur frequently and/or have more than a constant-length pattern match.
static bool foldUnusualPatterns(Function &F, DominatorTree &DT,
                                TargetTransformInfo &TTI,
                                TargetLibraryInfo &TLI, AliasAnalysis &AA) {
  bool MadeChange = false;
  
  if(F.getName().str()=="reverse"){
    errs() << "We won't check this function!" << "\n";
    return false;
  }
  
  if(UseOptionOne && !UseOptionTwo){
    bool crc_flag=tryToRecognizeCRC32_v1(F.back().back());
    if(crc_flag)
      errs() << "CRC32 algorithm has been recognised!" << "\n";   
  } else if(!UseOptionOne && UseOptionTwo){
    bool crc_flag=tryToRecognizeCRC32_v2(F.back().back());
    if(crc_flag)
      errs() << "CRC32 algorithm has been recognised!" << "\n";
  } else if(UseOptionOne && UseOptionTwo){
    errs() << "Sorry, but you can't use both options for crc algorithm recognition!\n";
  }

  Module *M=F.getParent();
  for(Function &F: *M){
    for (BasicBlock &BB : F) {
      // Ignore unreachable basic blocks.
      if (!DT.isReachableFromEntry(&BB))
        continue;
      
      //errs() << "Hello from here!" << "\n";
      const DataLayout &DL = F.getParent()->getDataLayout();

      // Walk the block backwards for efficiency. We're matching a chain of
      // use->defs, so we're more likely to succeed by starting from the bottom.
      // Also, we want to avoid matching partial patterns.
      // TODO: It would be more efficient if we removed dead instructions
      // iteratively in this loop rather than waiting until the end.
      for (Instruction &I : make_early_inc_range(llvm::reverse(BB))) {
        MadeChange |= foldAnyOrAllBitsSet(I);
        MadeChange |= foldGuardedFunnelShift(I, DT);
        MadeChange |= tryToRecognizePopCount(I);
        
        //bool flag1=tryToRecognizeTableBasedCRC32(I);
        //MadeChange |= flag1;
        //if(flag1)
        //  errs() << "Function we have created seems to work properly!\n";

        MadeChange |= tryToFPToSat(I, TTI);
        //MadeChange |= tryToRecognizeTableBasedCttz(I);
        bool recognised=tryToRecognizeTableBasedCttz(I);
        if(recognised){
          MadeChange |=recognised;
          //errs() << "Mission completed!" << "\n";
        } else {
          MadeChange |=recognised;
          //errs() << "Mission is still not completed!" << "\n";
        }
        MadeChange |= foldConsecutiveLoads(I, DL, TTI, AA, DT);
        MadeChange |= foldPatternedLoads(I, DL);
        // NOTE: This function introduces erasing of the instruction `I`, so it
        // needs to be called at the end of this sequence, otherwise we may make
        // bugs.
        MadeChange |= foldSqrt(I, TTI, TLI);
      }
    }
  }
  // We're done with transforms, so remove dead instructions.
  if (MadeChange)
    for (BasicBlock &BB : F)
      SimplifyInstructionsInBlock(&BB);

  return MadeChange;
}

/// This is the entry point for all transforms. Pass manager differences are
/// handled in the callers of this function.
static bool runImpl(Function &F, AssumptionCache &AC, TargetTransformInfo &TTI,
                    TargetLibraryInfo &TLI, DominatorTree &DT,
                    AliasAnalysis &AA) {
  bool MadeChange = false;
  const DataLayout &DL = F.getParent()->getDataLayout();
  TruncInstCombine TIC(AC, TLI, DL, DT);
  MadeChange |= TIC.run(F);
  MadeChange |= foldUnusualPatterns(F, DT, TTI, TLI, AA);
  return MadeChange;
}

PreservedAnalyses AggressiveInstCombinePass::run(Function &F,
                                                 FunctionAnalysisManager &AM) {
  auto &AC = AM.getResult<AssumptionAnalysis>(F);
  auto &TLI = AM.getResult<TargetLibraryAnalysis>(F);
  auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
  auto &TTI = AM.getResult<TargetIRAnalysis>(F);
  auto &AA = AM.getResult<AAManager>(F);
  if (!runImpl(F, AC, TTI, TLI, DT, AA)) {
    // No changes, all analyses are preserved.
    return PreservedAnalyses::all();
  }
  // Mark all the analyses that instcombine updates as preserved.
  PreservedAnalyses PA;
  PA.preserveSet<CFGAnalyses>();
  //return PreservedAnalyses::none();
  return PA;
}
