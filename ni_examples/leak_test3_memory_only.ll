; Test 3: Secret-dependent memory access (no branch leakage, only memory leakage)
; Expected: same OBranch (no branches), different OLoad addresses
define i32 @main(i32 %secret) {
entry:
  %arr = alloca i32, i32 4
  %p0 = getelementptr i32, i32* %arr, i32 0
  %p1 = getelementptr i32, i32* %arr, i32 1
  %p2 = getelementptr i32, i32* %arr, i32 2
  %p3 = getelementptr i32, i32* %arr, i32 3
  store i32 10, i32* %p0
  store i32 20, i32* %p1
  store i32 30, i32* %p2
  store i32 40, i32* %p3
  %idx = srem i32 %secret, 4
  %data_ptr = getelementptr i32, i32* %arr, i32 %idx
  %val = load i32, i32* %data_ptr
  ret i32 %val
}
