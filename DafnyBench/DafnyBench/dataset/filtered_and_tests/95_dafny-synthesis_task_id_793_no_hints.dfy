method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}

method TestLastPosition1() {
  var arr := new int[5];
  arr[0] := 1; arr[1] := 2; arr[2] := 2; arr[3] := 3; arr[4] := 4;
  var pos := LastPosition(arr, 2);
  assert pos == 2;
}

method TestLastPosition2() {
  var arr := new int[4];
  arr[0] := 1; arr[1] := 3; arr[2] := 5; arr[3] := 7;
  var pos := LastPosition(arr, 4);
  assert pos == -1;
}
