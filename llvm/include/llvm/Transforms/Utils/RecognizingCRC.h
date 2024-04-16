#ifndef LLVM_TRANSFORMS_RECOGNIZINGCRC_RECOGNIZINGCRC_H
#define LLVM_TRANSFORMS_RECOGNIZINGCRC_RECOGNIZINGCRC_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class RecognizingCRCPass : public PassInfoMixin<RecognizingCRCPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_RECOGNIZINGCRC_RECOGNIZINGCRC_H
