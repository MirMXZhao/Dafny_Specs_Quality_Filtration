method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}

////////TESTS////////

method TestFindFirstOccurrence1() {
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 3, 5, 5, 7;
  var index := FindFirstOccurrence(arr, 5);
  assert index == 2;
}

method TestFindFirstOccurrence2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 2, 4, 6, 8;
  var index := FindFirstOccurrence(arr, 9);
  assert index == -1;
}
