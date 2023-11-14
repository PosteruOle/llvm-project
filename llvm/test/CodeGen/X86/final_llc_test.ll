; RUN: llc -debug %s 2>&1 | FileCheck %s

; CHECK: Successfully custom legalized node
; CHECK-NEXT: ... replacing: t3: i32 = add t2, t2
; CHECK-NEXT: with:      t9: i32 = mul t2, Constant:i32<2>

define i32 @test(i32 %0) {
  %res = add i32 %0, %0
  ret i32 %res
}
