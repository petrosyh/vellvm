; Test 1: Simple secret-dependent branch
; Expected: different OBranch for different secrets
define i32 @main(i32 %secret) {
entry:
  %cmp = icmp sgt i32 %secret, 50
  br i1 %cmp, label %then, label %else
then:
  ret i32 1
else:
  ret i32 0
}
