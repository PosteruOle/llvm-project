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
       errs()<< "Instruction: " << I.getName() << "\n"; 
       if(II && (II->getIntrinsicID() == Intrinsic::cttz))
         countCttzIntrinsicAppearance++;
    }
  }
  //errs() << "\n-------------------------------\n";
  errs() << "Total number of cttz intrinsic appearances is equal to: " << countCttzIntrinsicAppearance << ".\n";

  return PreservedAnalyses::all();
}