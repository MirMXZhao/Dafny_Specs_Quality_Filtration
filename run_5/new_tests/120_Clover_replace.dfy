method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{}

////////TESTS////////

method TestReplace1() {
  var arr := new int[5] [3, 7, 2, 9, 1];
  replace(arr, 5);
  assert arr[0] == 3;
  assert arr[1] == -1;
  assert arr[2] == 2;
  assert arr[3] == -1;
  assert arr[4] == 1;
}

method TestReplace2() {
  var arr := new int[4] [1, 2, 3, 4];
  replace(arr, 10);
  assert arr[0] == 1;
  assert arr[1] == 2;
  assert arr[2] == 3;
  assert arr[3] == 4;
}
