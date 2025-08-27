function Sum(arr: array<int>, len: int): int
    reads arr
    requires arr.Length > 0 && 0 <= len <= arr.Length
{}

method SumArray(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    ensures sum == Sum(arr, arr.Length)
{}

////////TESTS////////

method TestSum1() {
  var arr := new int[3];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  var result := Sum(arr, 3);
  assert result == 6;
}

method TestSum2() {
  var arr := new int[4];
  arr[0] := 5;
  arr[1] := -2;
  arr[2] := 0;
  arr[3] := 3;
  var result := Sum(arr, 2);
  assert result == 3;
}

method TestSumArray1() {
  var arr := new int[3];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  var sum := SumArray(arr);
  assert sum == 6;
}

method TestSumArray2() {
  var arr := new int[4];
  arr[0] := 10;
  arr[1] := -5;
  arr[2] := 7;
  arr[3] := 2;
  var sum := SumArray(arr);
  assert sum == 14;
}
