; RUN: llc -debug %s 2>&1 | FileCheck %s

; CHECK: We are on the right track!
; CHECK-NEXT: We have found the first square!
; CHECK-NEXT: We have found the second square!
; CHECK-NEXT: We have successfully recognized binomial square!
; CHECK: We have successfully created nodes that will decrease binomial square implementation!

define i32 @test(i32 %0, i32 %1) {
  %square1 = mul i32 %0, %0
  %square2 = mul i32 %1, %1
  %mul = mul i32 %0, %1
  %mul2 = mul i32 %mul, 2
  %res1 = add i32 %square1, %mul2
  %res2 = add i32 %res1, %square2 
  ret i32 %res2
}

