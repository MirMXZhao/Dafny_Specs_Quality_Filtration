method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    requires 0 <= arr.Length < 10000
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    ensures multiset(arr[..]) == multiset(arr_sorted[..])
    modifies arr
{} 

predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{}

predicate pivot(arr: array<int>, pivot: int)
requires 0 <= pivot <= arr.Length
reads arr
{}

////////TESTS////////

method TestSortArray1() {
  var arr := new int[5];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  arr[3] := 1;
  arr[4] := 9;
  var arr_sorted := sortArray(arr);
  assert arr_sorted[..] == [1, 2, 5, 8, 9];
}

method TestSortArray2() {
  var arr := new int[3];
  arr[0] := 3;
  arr[1] := 1;
  arr[2] := 2;
  var arr_sorted := sortArray(arr);
  assert arr_sorted[..] == [1, 2, 3];
}
