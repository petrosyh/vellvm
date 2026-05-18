; Test 6: Branch leakage with different allocation patterns per branch
; Expected: different OBranch + different number of OStore events
define i32 @main(i32 %secret) {
entry:
  %cmp = icmp sgt i32 %secret, 0
  br i1 %cmp, label %positive, label %negative
positive:
  %a = alloca i32
  store i32 1, i32* %a
  %va = load i32, i32* %a
  ret i32 %va
negative:
  %b = alloca i32
  %c = alloca i32
  store i32 2, i32* %b
  store i32 3, i32* %c
  %vb = load i32, i32* %b
  %vc = load i32, i32* %c
  %sum = add i32 %vb, %vc
  ret i32 %sum
}
