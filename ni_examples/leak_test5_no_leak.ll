; Test 5: No leakage — secret used only in computation, not in branch or address
; Expected: identical traces for all secrets
define i32 @main(i32 %secret) {
entry:
  %x = alloca i32
  store i32 %secret, i32* %x
  %v = load i32, i32* %x
  %result = add i32 %v, 42
  ret i32 %result
}
