; Test 2: Nested secret-dependent branches
; Expected: different OBranch sequences for different secrets
define i32 @main(i32 %secret) {
entry:
  %cmp1 = icmp sgt i32 %secret, 50
  br i1 %cmp1, label %high, label %low
high:
  %cmp2 = icmp sgt i32 %secret, 75
  br i1 %cmp2, label %very_high, label %medium_high
very_high:
  ret i32 3
medium_high:
  ret i32 2
low:
  %cmp3 = icmp sgt i32 %secret, 25
  br i1 %cmp3, label %medium_low, label %very_low
medium_low:
  ret i32 1
very_low:
  ret i32 0
}
