#include "llvm/Transforms/Utils/PetarHelloWorld.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Regex.h"

using namespace llvm;
int count_Cttz_Intrinsic_Appearance=0;

PreservedAnalyses PetarHelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {

  
  Regex llvmcttzRegex("^llvm.cttz.*");
  errs() << "Function name: " << F.getName() << "\n";
  for(BasicBlock& BB: F){
    for(Instruction& I: BB){
      //errs()<< "Instruction: " << I.getName() << "\n";
      if(CallBase::classof(&I)){
        CallBase* callBase = (CallBase*) &I;
        StringRef functionName = callBase->getCalledFunction()->getName();
        //errs() << "Instruction name: " << functionName << "\n";
        if(llvmcttzRegex.match(functionName)){
          errs() << "Look what we have found -> " << functionName << "\n";
          count_Cttz_Intrinsic_Appearance++;
        }  
      }     
    }
  }
  //errs() << "\n-------------------------------\n";
  errs() << "Total number of cttz intrinsic appearances is equal to: " << count_Cttz_Intrinsic_Appearance << ".\n";

  return PreservedAnalyses::all();
}