#include "llvm/Transforms/Utils/PetarHelloWorld.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
//---------------------------------
#include "llvm/Support/Regex.h"

using namespace llvm;
int count_cttz_intrinsic_appearance=0;

PreservedAnalyses PetarHelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {
  Regex llvmcttzRegex("^llvm.cttz.*");
  errs() << "Function name: " << F.getName() << "\n";
  errs() << "\n-------------------------------\n";
  errs() << "Instructions within this function!\n";
  for(BasicBlock& BB: F){
    for(Instruction& I: BB){
       errs()<< I.getName() << "\n";
       
       if(CallBase::classof(&I)){
          CallBase* callBase = (CallBase*) &I;
          StringRef functionName = callBase->getCalledFunction()->getName();
          if(llvmcttzRegex.match(functionName))
            count_cttz_intrinsic_appearance++;
       }     
    }
  }
  errs() << "\n-------------------------------\n";
  errs() << "Total number of cttz intrinsic appearances is equal to: " << count_cttz_intrinsic_appearance << ".\n";

  return PreservedAnalyses::all();
}