#include "llvm/Transforms/Utils/RecognizingCRC.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"
#include "llvm/Transforms/Utils/Local.h"
#include <cassert>
#include <cstring>

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IntrinsicsRISCV.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;
using namespace PatternMatch;

using namespace llvm;

static cl::opt<bool> UseOptionOne("use-option-one", cl::init(false), cl::Hidden,
                                  cl::desc("Using option one!"));

static cl::opt<bool> UseOptionTwo("use-option-two", cl::init(false), cl::Hidden,
                                  cl::desc("Using option two!"));

static bool tryToRecognizeCRC32_v1(Instruction &I) {
  ReturnInst *RI = dyn_cast<ReturnInst>(&I);
  ReturnInst *RIfinal = dyn_cast<ReturnInst>(&I);
  if (!RI || !RIfinal)
    return false;

  LoadInst *LI = dyn_cast<LoadInst>(RI->getPrevNode());
  LoadInst *LIfinal = dyn_cast<LoadInst>(RI->getPrevNode());
  if (!LI || !LIfinal)
    return false;

  errs() << "for.end: checked\n";

  BasicBlock *BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BranchInst *BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  StoreInst *SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  Instruction *II = dyn_cast<Instruction>(SI->getPrevNode());
  if (!II)
    return false;

  Value *help1;
  Value *help2;
  if (!match(II, m_Add(m_Value(help1), m_Value(help2))))
    return false;

  LI = dyn_cast<LoadInst>(II->getPrevNode());
  if (!LI)
    return false;

  errs() << "for.inc: checked\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  errs() << "if.end25: checked\n";

  BB = dyn_cast<BasicBlock>(BI->getParent()->getPrevNode());
  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  TruncInst *TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_And(m_Value(help1), m_SpecificInt(32767))))
    return false;

  ZExtInst *ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  errs() << "if.else21: checked\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  // We should somehow recognize -32768 here!
  if (!match(II, m_Or(m_Value(help1), m_Value(help2))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  errs() << "if.then18: checked\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICmpInst *ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  LI = dyn_cast<LoadInst>(ICMPI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  errs() << "if.else: checked!\n";

  BB = dyn_cast<BasicBlock>(SI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_Xor(m_Value(help1), m_SpecificInt(16386))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  errs() << "if.then: checked!\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  ZI = dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_Xor(m_Value(help1), m_Value(help2))))
    return false;

  II = dyn_cast<Instruction>(II->getPrevNode());
  if (!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  TI = dyn_cast<TruncInst>(ZI->getPrevNode());
  if (!TI)
    return false;

  LI = dyn_cast<LoadInst>(TI->getPrevNode());
  if (!LI)
    return false;

  II = dyn_cast<Instruction>(LI->getPrevNode());
  if (!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  errs() << "for.body: checked!\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  ZI = dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  errs() << "for.cond: checked!\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  // Here we have to match 6 more consecutive store instructions and 5
  // consecutive alloca instructions!
  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  // Last thing we have to match are 5 alloca instructions!
  AllocaInst *AI = dyn_cast<AllocaInst>(SI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  errs()
      << "Original unoptimized form of CRC32 algorithm has been recognized!\n";
  Value *argument1 = LIfinal->getFunction()->getArg(0);
  Value *argument2 = LIfinal->getFunction()->getArg(1);
  Type *ArgType1 = argument1->getType();
  Type *ArgType2 = argument2->getType();
  IRBuilder<> B(LIfinal);

  // Something to remember because it's very important!
  // Here is hidden a another aproach for replacing unoptimized crc with
  // optimized version! auto CRC8 = B.CreateIntrinsic(Intrinsic::crc8, {},
  // {argument1, argument2});
  auto CRC8 =
      B.CreateIntrinsic(Intrinsic::riscv_crc_petar, {}, {argument1, argument2});
  LIfinal->replaceAllUsesWith(CRC8);
  Function *F = LIfinal->getFunction();

  BasicBlock *bb_help10 = RIfinal->getParent()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode();
  BasicBlock *bb_help9 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help8 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help7 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help6 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help5 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help4 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help3 =
      RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help2 = RIfinal->getParent()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help1 = RIfinal->getParent()->getPrevNode();
  DeleteDeadBlocks({bb_help1, bb_help2, bb_help3, bb_help4, bb_help5, bb_help6,
                    bb_help7, bb_help8, bb_help9, bb_help10});

  F->back().back().getPrevNode()->eraseFromParent();

  // We will save this part of code! Just to have track of what we have created
  // so far!
  errs() << "-----------------------------------------\n";
  errs() << F->getName() << ": \n";
  for (BasicBlock &BBIT : *F) {
    for (Instruction &IIT : BBIT) {
      errs() << IIT << "\n";
    }
  }
  errs() << "-----------------------------------------\n";

  return true;
}

static bool tryToRecognizeCRC32_v2(Instruction &I) {
  ReturnInst *RI = dyn_cast<ReturnInst>(&I);
  ReturnInst *RIfinal = dyn_cast<ReturnInst>(&I);
  if (!RI || !RIfinal)
    return false;

  LoadInst *LI = dyn_cast<LoadInst>(RI->getPrevNode());
  LoadInst *LIfinal = dyn_cast<LoadInst>(RI->getPrevNode());
  if (!LI || !LIfinal)
    return false;

  BasicBlock *BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BranchInst *BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  StoreInst *SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  Instruction *II = dyn_cast<Instruction>(SI->getPrevNode());
  if (!II)
    return false;

  Value *help1;
  Value *help2;
  //II->dump();
  if (!match(II, m_Add(m_Load(m_Value(help1)), m_SpecificInt(1))))
    return false;

  LI = dyn_cast<LoadInst>(II->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  BB = dyn_cast<BasicBlock>(BI->getParent()->getPrevNode());
  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  //SI->dump();

  TruncInst *TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  // For some reason we could not see trunc instruction!
  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_And((m_Value(help1)), m_SpecificInt(32767))))
    return false;

  //II->dump();

  ZExtInst *ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  //II->dump();

  // We should somehow recognize -32768 here!
  if (!match(II, m_Or(m_Value(help1), m_Value(help2))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  //errs() << "Hi there! We are here!\n";

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICmpInst *ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  LI = dyn_cast<LoadInst>(ICMPI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  BB = dyn_cast<BasicBlock>(SI->getParent()->getPrevNode());
  if (!BB)
    return false;

  //errs() << "Hi there! We are here! Line number 57\n";

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_Xor(m_Value(help1), m_SpecificInt(16386))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return ZI;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  //errs() << "Hi there! We are here! Line number 48\n";

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  ZI = dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_AShr(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  SI = dyn_cast<StoreInst>(LI->getPrevNode());
  if (!SI)
    return false;

  TI = dyn_cast<TruncInst>(SI->getPrevNode());
  if (!TI)
    return false;

  II = dyn_cast<Instruction>(TI->getPrevNode());
  if (!match(II, m_Xor(m_Value(help1), m_Value(help2))))
    return false;

  II = dyn_cast<Instruction>(II->getPrevNode());
  if (!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  TI = dyn_cast<TruncInst>(ZI->getPrevNode());
  if (!TI)
    return false;

  LI = dyn_cast<LoadInst>(TI->getPrevNode());
  if (!LI)
    return false;

  II = dyn_cast<Instruction>(LI->getPrevNode());
  if (!match(II, m_And(m_Value(help1), m_SpecificInt(1))))
    return false;

  ZI = dyn_cast<ZExtInst>(II->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  ICMPI = dyn_cast<ICmpInst>(BI->getPrevNode());
  if (!ICMPI)
    return false;

  ZI = dyn_cast<ZExtInst>(ICMPI->getPrevNode());
  if (!ZI)
    return false;

  LI = dyn_cast<LoadInst>(ZI->getPrevNode());
  if (!LI)
    return false;

  BB = dyn_cast<BasicBlock>(LI->getParent()->getPrevNode());
  if (!BB)
    return false;

  BI = dyn_cast<BranchInst>(&BB->back());
  if (!BI)
    return false;

  // Here we have to match 6 more consecutive store instructions and 5
  // consecutive alloca instructions!
  SI = dyn_cast<StoreInst>(BI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  SI = dyn_cast<StoreInst>(SI->getPrevNode());
  if (!SI)
    return false;

  // Last thing we have to match are 5 alloca instructions!
  AllocaInst *AI = dyn_cast<AllocaInst>(SI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  AI = dyn_cast<AllocaInst>(AI->getPrevNode());
  if (!AI)
    return false;

  errs()
      << "Original unoptimized form of CRC32 algorithm has been recognized!\n";
  Value *argument1 = LIfinal->getFunction()->getArg(0);
  Value *argument2 = LIfinal->getFunction()->getArg(1);
  Type *ArgType1 = argument1->getType();
  Type *ArgType2 = argument2->getType();
  IRBuilder<> B(LIfinal);

  BasicBlock *bb_help10 = RIfinal->getParent()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode()
                              ->getPrevNode();
  BasicBlock *bb_help9 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help8 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help7 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help6 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help5 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help4 = RIfinal->getParent()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode()
                             ->getPrevNode();
  BasicBlock *bb_help3 =
      RIfinal->getParent()->getPrevNode()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help2 = RIfinal->getParent()->getPrevNode()->getPrevNode();
  BasicBlock *bb_help1 = RIfinal->getParent()->getPrevNode();
  DeleteDeadBlocks({bb_help1, bb_help2, bb_help3, bb_help4, bb_help5, bb_help6,
                    bb_help7, bb_help8, bb_help9, bb_help10});

  IRBuilder<> Builder(LIfinal);
  Function *F = LIfinal->getFunction();
  LIfinal->getParent()->setName("entry");
  AllocaInst *AI1 = Builder.CreateAlloca(ArgType1, nullptr, "data.addr");
  AllocaInst *AI2 = Builder.CreateAlloca(ArgType2, nullptr, "_crc.addr");
  AllocaInst *AI3 = Builder.CreateAlloca(ArgType1, nullptr, "i");
  AllocaInst *AI4 = Builder.CreateAlloca(ArgType1, nullptr, "x16");
  AllocaInst *AI5 = Builder.CreateAlloca(ArgType1, nullptr, "carry");
  AllocaInst *AI6 = Builder.CreateAlloca(Builder.getInt64Ty(), nullptr, "crc");
  StoreInst *SI1 = Builder.CreateStore(argument1, AI1);
  StoreInst *SI2 = Builder.CreateStore(argument2, AI2);
  StoreInst *SI3 = Builder.CreateStore(Builder.getInt8(0), AI3);
  StoreInst *SI4 = Builder.CreateStore(Builder.getInt8(0), AI4);
  StoreInst *SI5 = Builder.CreateStore(Builder.getInt8(0), AI5);
  LoadInst *LI1 = Builder.CreateLoad(ArgType2, AI2, "");
  Value *ZI1 = Builder.CreateZExt(LI1, Builder.getInt64Ty(), "conv");
  StoreInst *SI6 = Builder.CreateStore(ZI1, AI6);
  LoadInst *LI2 = Builder.CreateLoad(Builder.getInt8Ty(), AI1, "");
  Value *ZI2 = Builder.CreateZExt(LI2, Builder.getInt64Ty(), "conv1");
  LoadInst *LI3 = Builder.CreateLoad(Builder.getInt64Ty(), AI6, "");
  Value *XOR1 = Builder.CreateXor(LI3, ZI2, "xor");
  StoreInst *SI7 = Builder.CreateStore(XOR1, AI6);
  StoreInst *SI8 = Builder.CreateStore(Builder.getInt8(0), AI3);

  BasicBlock *ForEndBB =
      BasicBlock::Create(F->getContext(), "for.end", F, nullptr);
  Instruction *I1 = LIfinal;
  Instruction *I2 = LIfinal->getNextNode();
  I1->removeFromParent();
  I2->removeFromParent();
  I1->insertInto(ForEndBB, ForEndBB->end());
  I2->insertInto(ForEndBB, ForEndBB->end());

  // IRBuilder<> Builder1(SI8->getParent(), SI8->getParent()->end());
  // BranchInst *BI1=Builder1.CreateBr(ForCondBB);

  // I think we can start this way!
  BasicBlock *ForCondBB =
      BasicBlock::Create(F->getContext(), "for.cond", F, ForEndBB);
  IRBuilder<> ForCondBuilder(ForCondBB, ForCondBB->end());
  BasicBlock *ForBodyBB =
      BasicBlock::Create(F->getContext(), "for.body", F, ForEndBB);
  IRBuilder<> ForBodyBuilder(ForBodyBB, ForBodyBB->end());
  BasicBlock *ForIncBB =
      BasicBlock::Create(F->getContext(), "for.inc", F, ForEndBB);
  IRBuilder<> ForIncBuilder(ForIncBB, ForIncBB->end());

  IRBuilder<> Builder1(SI8->getParent(), SI8->getParent()->end());
  BranchInst *BI1 = Builder1.CreateBr(ForCondBB);

  // Everything is okay with creation of "for.cond" basic block!
  LoadInst *LI4 = ForCondBuilder.CreateLoad(ForCondBuilder.getInt8Ty(), AI6);
  Value *ZI3 =
      ForCondBuilder.CreateZExt(LI4, ForCondBuilder.getInt32Ty(), "conv2");
  Value *ICI1 = ForCondBuilder.CreateICmp(llvm::CmpInst::ICMP_SLT, ZI3,
                                          ForCondBuilder.getInt32(8), "cmp");
  BranchInst *BI2 = ForCondBuilder.CreateCondBr(ICI1, ForBodyBB, ForEndBB);

  // Everything is okay with creation of "for.body" basic block!
  LoadInst *LI5 = ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *TI1 =
      ForBodyBuilder.CreateTrunc(LI5, ForBodyBuilder.getInt8Ty(), "conv4");
  Value *ZI4 =
      ForBodyBuilder.CreateZExt(TI1, ForCondBuilder.getInt32Ty(), "conv5");
  Value *And1 =
      ForBodyBuilder.CreateAnd(ZI4, ForBodyBuilder.getInt32(1), "and");
  Value *TI2 =
      ForBodyBuilder.CreateTrunc(And1, ForBodyBuilder.getInt8Ty(), "conv6");
  StoreInst *SI9 = ForBodyBuilder.CreateStore(TI2, AI4);
  LoadInst *LI6 = ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI1);
  Value *ZI5 =
      ForBodyBuilder.CreateZExt(LI6, ForCondBuilder.getInt32Ty(), "conv7");
  Value *Ashr1 =
      ForBodyBuilder.CreateAShr(ZI5, ForBodyBuilder.getInt32(1), "shr");
  Value *TI3 =
      ForBodyBuilder.CreateTrunc(Ashr1, ForBodyBuilder.getInt8Ty(), "conv8");
  StoreInst *SI10 = ForBodyBuilder.CreateStore(TI3, AI1);
  LoadInst *LI7 = ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *Ashr2 =
      ForBodyBuilder.CreateAShr(LI7, ForBodyBuilder.getInt64(1), "shr9");
  StoreInst *SI11 = ForBodyBuilder.CreateStore(Ashr2, AI6);
  LoadInst *LI8 = ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI4);
  Value *ZI6 =
      ForBodyBuilder.CreateZExt(LI8, ForCondBuilder.getInt32Ty(), "conv10");
  Value *And2 =
      ForBodyBuilder.CreateAnd(ZI6, ForBodyBuilder.getInt32(1), "and11");
  Value *ICI2 = ForBodyBuilder.CreateICmp(llvm::CmpInst::ICMP_NE, And2,
                                          ForCondBuilder.getInt32(0), "tobool");
  Value *ZI7 = ForBodyBuilder.CreateZExt(ICI2, ForCondBuilder.getInt64Ty(), "");
  Value *Select1 = ForBodyBuilder.CreateSelect(
      ICI2, ForBodyBuilder.getInt32(40961), ForBodyBuilder.getInt32(0));
  Value *Sext1 =
      ForBodyBuilder.CreateSExt(Select1, ForBodyBuilder.getInt64Ty(), "conv12");
  LoadInst *LI9 = ForBodyBuilder.CreateLoad(ForBodyBuilder.getInt64Ty(), AI6);
  Value *XOR2 = ForBodyBuilder.CreateXor(LI9, Sext1, "xor13");
  StoreInst *SI12 = ForBodyBuilder.CreateStore(XOR2, AI6);
  BranchInst *BI3 = ForBodyBuilder.CreateBr(ForIncBB);

  // Everything is okay with creation of "for.inc" basic block!
  LoadInst *LI10 = ForIncBuilder.CreateLoad(ForBodyBuilder.getInt8Ty(), AI3);
  Value *Add1 = ForIncBuilder.CreateAdd(LI10, ForIncBuilder.getInt8(1), "inc");
  StoreInst *SI20 = ForIncBuilder.CreateStore(Add1, AI3);
  // We need to check this branch instruction again!
  BranchInst *BI4 = ForIncBuilder.CreateBr(ForCondBB);

  // Last, we have to change a couple of instructions within "for.end" basic
  // block!
  IRBuilder<> ForEndBuilder(LIfinal);
  LoadInst *LI11 = ForEndBuilder.CreateLoad(B.getInt64Ty(), AI6);
  Value *TI20 = ForEndBuilder.CreateTrunc(LI11, B.getInt16Ty(), "conv14");

  LIfinal->replaceAllUsesWith(TI20);

  F->back().back().getPrevNode()->eraseFromParent();
  // We will save this part of code! Just to have track of what we have created
  // so far!

  errs() << "-----------------------------------------\n";
  errs() << "Function name: " << F->getName() << " \n";
  errs() << "Function body:\n";
  for (BasicBlock &BBIT : *F) {
    errs() << BBIT.getName() << ":\n";
    for (Instruction &IIT : BBIT) {
      errs() << IIT << "\n";
    }
  }
  errs() << "-----------------------------------------\n";

  return true;
}

PreservedAnalyses RecognizingCRCPass::run(Function &F,
                                          FunctionAnalysisManager &AM) {

  if (UseOptionOne && !UseOptionTwo) {
    errs() << "You choose the first option!\n";
    bool crc_flag = tryToRecognizeCRC32_v1(F.back().back());
    if (crc_flag)
      errs() << "CRC32 algorithm has been recognised!"
             << "\n";
  } else if (!UseOptionOne && UseOptionTwo) {
    errs() << "You choose the second option!\n";
    bool crc_flag = tryToRecognizeCRC32_v2(F.back().back());
    if (crc_flag)
      errs() << "CRC32 algorithm has been recognised!"
             << "\n";
  } else if (UseOptionOne && UseOptionTwo) {
    errs() << "Sorry, but you can't use both options for crc algorithm "
              "recognition!\n";
  }

  return PreservedAnalyses::all();
}
