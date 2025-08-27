method KthElement(arr: array<int>, k: int) returns (result: int)
  requires 1 <= k <= arr.Length
  ensures result == arr[k - 1]
{}

////////TESTS////////

method TestKthElement1() {
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 10, 20, 30, 40, 50;
  var result := KthElement(arr, 3);
  assert result == 30;
}

method TestKthElement2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 7, 14, 21, 28;
  var result := KthElement(arr, 1);
  assert result == 7;
}
