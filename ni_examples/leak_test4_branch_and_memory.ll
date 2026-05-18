; Test 4: Both branch AND memory leakage
; Expected: different OBranch AND different OLoad/OStore patterns
define i32 @main(i32 %secret) {
entry:
  %arr = alloca i32, i32 2
  %p0 = getelementptr i32, i32* %arr, i32 0
  %p1 = getelementptr i32, i32* %arr, i32 1
  store i32 100, i32* %p0
  store i32 200, i32* %p1
  %cmp = icmp sgt i32 %secret, 50
  br i1 %cmp, label %then, label %else
then:
  %v1 = load i32, i32* %p0
  ret i32 %v1
else:
  %v2 = load i32, i32* %p1
  ret i32 %v2
}
