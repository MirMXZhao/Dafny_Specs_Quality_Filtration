method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}

////////TESTS////////

method TestLastPosition1() {
  var arr := new int[5];
  arr[0] := 1; arr[1] := 2; arr[2] := 3; arr[3] := 3; arr[4] := 5;
  var pos := LastPosition(arr, 3);
  assert pos == 3;
}

method TestLastPosition2() {
  var arr := new int[4];
  arr[0] := 1; arr[1] := 2; arr[2] := 4; arr[3] := 5;
  var pos := LastPosition(arr, 3);
  assert pos == -1;
}
