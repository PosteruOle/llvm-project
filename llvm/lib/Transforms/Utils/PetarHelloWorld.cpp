#include "llvm/Transforms/Utils/PetarHelloWorld.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

using namespace llvm;

PreservedAnalyses PetarHelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {

  errs() << "Function name: " << F.getName() << "\n";
  errs() << "\n-------------------------------\n";
  errs() << "Instructions within this function!\n";
  for(BasicBlock& BB: F){
    for(Instruction& I: BB){
       errs()<< I.getName() << "\n";
    }
  }
  errs() << "\n-------------------------------\n";

  return PreservedAnalyses::all();
}
