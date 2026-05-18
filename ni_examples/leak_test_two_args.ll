; Two-argument main for testing -interpret-obs-args.
; Branches on whether the first arg is greater than the second.
define i32 @main(i32 %a, i32 %b) {
entry:
  %cmp = icmp sgt i32 %a, %b
  br i1 %cmp, label %then, label %else
then:
  ret i32 1
else:
  ret i32 0
}
