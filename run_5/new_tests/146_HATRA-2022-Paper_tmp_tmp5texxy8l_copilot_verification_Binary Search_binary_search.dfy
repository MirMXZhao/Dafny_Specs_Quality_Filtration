method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{}

predicate sorted(a: array<int>)
reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] 
}

predicate distinct(arr: array<int>)
    reads arr
{
    forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] != arr[j]
}

predicate not_found(arr: array<int>, target: int)
reads arr
{
    (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}

predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{}

////////TESTS////////

method TestBinarySearch1() {
  var arr := new int[5];
  arr[0] := 1; arr[1] := 3; arr[2] := 5; arr[3] := 7; arr[4] := 9;
  var index := BinarySearch(arr, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var arr := new int[4];
  arr[0] := 2; arr[1] := 4; arr[2] := 6; arr[3] := 8;
  var index := BinarySearch(arr, 3);
  assert index == -1;
}
