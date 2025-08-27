method swap(arr: array<int>, i: int, j: int)
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
{}

////////TESTS////////

method TestSwap1() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 10, 20, 30, 40;
  swap(arr, 1, 3);
  assert arr[1] == 40 && arr[3] == 20;
  assert arr[0] == 10 && arr[2] == 30;
}

method TestSwap2() {
  var arr := new int[3];
  arr[0], arr[1], arr[2] := 5, 15, 25;
  swap(arr, 0, 2);
  assert arr[0] == 25 && arr[2] == 5;
  assert arr[1] == 15;
}
