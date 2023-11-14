#ifndef LLVM_TRANSFORMS_EXPRESSION_OPTIMIZER_H
#define LLVM_TRANSFORMS_EXPRESSION_OPTIMIZER_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class ExpressionOptimizerPass : public PassInfoMixin<ExpressionOptimizerPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_EXPRESSION_OPTIMIZER