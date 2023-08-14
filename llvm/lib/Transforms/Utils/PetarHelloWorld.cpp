#include "llvm/Transforms/Utils/PetarCountCttz.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

using namespace llvm;
int countCttzIntrinsicAppearance=0;

PreservedAnalyses PetarCountCttzPass::run(Function &F, FunctionAnalysisManager &AM) {

  errs() << "Function name: " << F.getName() << "\n";
  //errs() << "\n-------------------------------\n";
  //errs() << "Instructions within this function!\n";
  for(BasicBlock& BB: F){
    errs() << "Here?!\n";
    errs() << "Basic block: " << BB.getName() << "...\n";
    for(Instruction& I: BB){
<<<<<<< HEAD
      //errs()<< "Instruction: " << I.getName() << "\n";
      errs() << "Instruction value name: " << I.getValueName() << "\n";
      errs() << "Instruction type: " << I.getType() << "\n";
      //errs() << CallBase::classof(&I) << "\n"; 
      if(CallBase::classof(&I)){
        CallBase* callBase = (CallBase*) &I;
        StringRef functionName = callBase->getCalledFunction()->getName();
        //errs() << "Instruction name: " << functionName << "\n";
        if(llvmcttzRegex.match(functionName)){
          errs() << "Look what we have found -> " << functionName << "\n";
          count_cttz_intrinsic_appearance++;
        }  
      }     
=======
       errs()<< "Instruction: " << I.getName() << "\n"; 
       if(II && (II->getIntrinsicID() == Intrinsic::cttz))
         countCttzIntrinsicAppearance++;
>>>>>>> 086aa55cc9827a9e7d8bafaf9a3311eb3700250c
    }
  }
  //errs() << "\n-------------------------------\n";
  errs() << "Total number of cttz intrinsic appearances is equal to: " << countCttzIntrinsicAppearance << ".\n";

  return PreservedAnalyses::all();
}