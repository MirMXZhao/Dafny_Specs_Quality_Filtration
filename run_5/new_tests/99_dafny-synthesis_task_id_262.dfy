method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}

////////TESTS////////

method TestSplitArray1() {
  var arr := new int[5];
  arr[0] := 1; arr[1] := 2; arr[2] := 3; arr[3] := 4; arr[4] := 5;
  var firstPart, secondPart := SplitArray(arr, 2);
  assert firstPart == [1, 2];
  assert secondPart == [3, 4, 5];
}

method TestSplitArray2() {
  var arr := new int[4];
  arr[0] := 10; arr[1] := 20; arr[2] := 30; arr[3] := 40;
  var firstPart, secondPart := SplitArray(arr, 0);
  assert firstPart == [];
  assert secondPart == [10, 20, 30, 40];
}
