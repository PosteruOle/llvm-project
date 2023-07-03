#ifndef LLVM_TRANSFORMS_PETARNEW_LLVMCTTZCOUNT_H
#define LLVM_TRANSFORMS_PETARNEW_LLVMCTTZCOUNT_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class PetarCountCttzPass : public PassInfoMixin<PetarCountCttzPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_HELLONEW_HELLOWORLD_H
