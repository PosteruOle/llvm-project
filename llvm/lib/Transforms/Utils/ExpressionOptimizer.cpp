#include "llvm/Transforms/Utils/ExpressionOptimizer.h"
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
#include <vector>
#include <algorithm>
#include <cstring>

using namespace llvm;
using namespace PatternMatch;

std::vector<StringRef> checkedFunctions;

bool findBinomialSquare(Instruction &I){
    Function *F=I.getFunction();
    
    for(StringRef name: checkedFunctions){
        if(F->getName()==name)
            return false;
    }

    ReturnInst *RI=dyn_cast<ReturnInst>(&I);
    if(!RI)
        return false;
    Instruction *II=dyn_cast<Instruction>(RI->getPrevNode());
    Instruction *IIfinal=dyn_cast<Instruction>(RI->getPrevNode());
    Value *help1;
    Value *help2;
    Value *a;
    Value *b;
    
    if(!match(II, m_Add(m_Add(m_Mul(m_Load(m_Value(a)), m_Load(m_Deferred(a))), m_Mul(m_Mul(m_SpecificInt(2), m_Load(m_Deferred(a))), m_Load(m_Value(b)))), 
        m_Mul(m_Load(m_Deferred(b)), m_Load(m_Deferred(b))))))
        return false;
    
    II=dyn_cast<Instruction>(II->getPrevNode());
    if(!match(II, m_Mul(m_Load(m_Value(help1)), m_Load(m_Deferred(help1)))))
        return false;

    LoadInst *LI=dyn_cast<LoadInst>(II->getPrevNode());
    if(!LI)
        return false;

    LI=dyn_cast<LoadInst>(LI->getPrevNode());
    if(!LI)
        return false;        
    
    II=dyn_cast<Instruction>(LI->getPrevNode());
    if(!match(II, m_Add(m_Value(help1), m_Value(help2))))
        return false;

    II=dyn_cast<Instruction>(II->getPrevNode());
    if(!match(II, m_Mul(m_Value(help1), m_Value(help2))))
        return false;

    LI=dyn_cast<LoadInst>(II->getPrevNode());
    if(!LI)
        return false;

    II=dyn_cast<Instruction>(LI->getPrevNode());
    if(!match(II, m_Mul(m_SpecificInt(2), m_Value(help2))))
        return false;        

    LI=dyn_cast<LoadInst>(II->getPrevNode());
    if(!LI)
        return false; 

    II=dyn_cast<Instruction>(LI->getPrevNode());

    if(!match(II, m_Mul(m_Load(m_Value(help1)), m_Load(m_Deferred(help1)))))
        return false;

    LI=dyn_cast<LoadInst>(II->getPrevNode());
    if(!LI)
        return false;

    LI=dyn_cast<LoadInst>(LI->getPrevNode());
    if(!LI)
        return false;

    StoreInst *SI=dyn_cast<StoreInst>(LI->getPrevNode());
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

    checkedFunctions.push_back(F->getName());
    Value *argument1=F->getArg(0);
    Value *argument2=F->getArg(1);
    
    IRBuilder<> B(IIfinal);
    Module *M=F->getParent();
    Function *callee;
    for(Function &FF: *M){
        if(FF.getName()=="f2"){
            callee=&FF;
        }    
    }

    auto f2_call=B.CreateCall(FunctionCallee(callee), {argument1, argument2});
    IIfinal->replaceAllUsesWith(f2_call);
    Instruction *previousInst=dyn_cast<Instruction>(IIfinal->getPrevNode());
    Instruction *nextInst=dyn_cast<Instruction>(IIfinal->getNextNode());
    BasicBlock *BB=IIfinal->getParent();
    
    int count=1;
    
    for(BasicBlock::reverse_iterator it=BB->rbegin();it!=BB->rend();){
        Instruction& inst_to_remove=*it;

        if(strcmp(inst_to_remove.getOpcodeName(), "store")==0 || strcmp(inst_to_remove.getOpcodeName(), "alloca")==0){
            it++;
            //errs() << inst_to_remove.getOpcodeName() << "\n";
            continue;
        }
        it++;

        if(&inst_to_remove!=previousInst && &inst_to_remove!=nextInst && inst_to_remove.isSafeToRemove()){
            inst_to_remove.eraseFromParent();
            count++;
        }
    }
    
    //We will hold those to command creations for the worst case!
    //LoadInst* new_load_1=new LoadInst(AI->getAllocatedType(), AI, "", f2_call);
    //LoadInst* new_load_2=new LoadInst(AI->getAllocatedType(), AI->getNextNode(), "", f2_call);
    
    IRBuilder Builder(f2_call);
    Value *StoreAddr1 = Builder.CreatePtrToInt(SI->getPointerOperand(), Builder.getInt32Ty());
    StoreInst *SInext=dyn_cast<StoreInst>(SI->getNextNode());
    Value *StoreAddr2 = Builder.CreatePtrToInt(SInext->getPointerOperand(), Builder.getInt32Ty());
    Value *Masked = Builder.CreateAdd(StoreAddr1, StoreAddr2);
    
    
    Value *mul_inst=Builder.CreateMul(Masked, Masked);
    f2_call->replaceAllUsesWith(mul_inst);
    f2_call->eraseFromParent();

    return true;     
}

PreservedAnalyses ExpressionOptimizerPass::run(Function &F, FunctionAnalysisManager &AM) {
    Module *M=F.getParent();
    for(Function &FF: *M){
        if(FF.empty())
            continue;

        BasicBlock& BB=FF.back();
        Instruction& I=BB.back();
        bool flag=findBinomialSquare(I);
        
        if(flag){
            errs() << "We have found a binomial square implementation!\n";
            break;
        }
    }

    return PreservedAnalyses::all();
}