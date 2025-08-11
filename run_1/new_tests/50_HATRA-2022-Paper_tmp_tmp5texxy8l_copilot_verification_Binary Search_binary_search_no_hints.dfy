method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{}

predicate sorted(a: array<int>)
reads a
{}

predicate distinct(arr: array<int>)
    reads arr
{}

predicate not_found(arr: array<int>, target: int)
reads arr
{}

predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{}

////////TESTS////////

method TestBinarySearch1() {
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 3, 5, 7, 9;
  var index := BinarySearch(arr, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 2, 4, 6, 8;
  var index := BinarySearch(arr, 3);
  assert index == -1;
}
