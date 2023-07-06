; RUN: opt -disable-output -passes=petarcountcttz %s 2>&1 | FileCheck %s

; CHECK: Function name: cttz_64_eq_select
; CHECK-NEXT: Total number of cttz intrinsic appearances is equal to: 1.
declare i64 @llvm.cttz.i64(i64, i1)
define i64 @cttz_64_eq_select(i64 %v) nounwind {

  %cnt = tail call i64 @llvm.cttz.i64(i64 %v, i1 true)
  %tobool = icmp eq i64 %v, 0
  %.op = add nuw nsw i64 %cnt, 6
  %add = select i1 %tobool, i64 5, i64 %.op
  ret i64 %add
}

; CHECK-NEXT: Function name: cttz_64_ne_select
; CHECK-NEXT: Total number of cttz intrinsic appearances is equal to: 2.
define i64 @cttz_64_ne_select(i64 %v) nounwind {

  %cnt = tail call i64 @llvm.cttz.i64(i64 %v, i1 true)
  %tobool = icmp ne i64 %v, 0
  %.op = add nuw nsw i64 %cnt, 6
  %add = select i1 %tobool, i64 %.op, i64 5
  ret i64 %add
}

; CHECK-NEXT: Function name: cttz_32_eq_select
; CHECK-NEXT: Total number of cttz intrinsic appearances is equal to: 3.
declare i32 @llvm.cttz.i32(i32, i1)
define i32 @cttz_32_eq_select(i32 %v) nounwind {

  %cnt = tail call i32 @llvm.cttz.i32(i32 %v, i1 true)
  %tobool = icmp eq i32 %v, 0
  %.op = add nuw nsw i32 %cnt, 6
  %add = select i1 %tobool, i32 5, i32 %.op
  ret i32 %add
}

; CHECK-NEXT: Function name: cttz_32_ne_select
; CHECK-NEXT: Total number of cttz intrinsic appearances is equal to: 4.
define i32 @cttz_32_ne_select(i32 %v) nounwind {

  %cnt = tail call i32 @llvm.cttz.i32(i32 %v, i1 true)
  %tobool = icmp ne i32 %v, 0
  %.op = add nuw nsw i32 %cnt, 6
  %add = select i1 %tobool, i32 %.op, i32 5
  ret i32 %add
}

