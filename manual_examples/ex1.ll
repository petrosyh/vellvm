define i32 @main(i32 %secret) {
entry:
  %arr = alloca i32, i32 4
  %ptr0 = getelementptr i32, i32* %arr, i32 0
  %ptr1 = getelementptr i32, i32* %arr, i32 1
  %ptr2 = getelementptr i32, i32* %arr, i32 2
  store i32 10, i32* %ptr0
  store i32 20, i32* %ptr1
  store i32 30, i32* %ptr2
  %idx = srem i32 %secret, 3
  %data_ptr = getelementptr i32, i32* %arr, i32 %idx
  %val = load i32, i32* %data_ptr
  ret i32 %val
}