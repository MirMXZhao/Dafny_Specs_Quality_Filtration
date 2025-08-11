method binarySearch(a:array<int>, val:int) returns (pos:int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures 0 <= pos < a.Length ==> a[pos] == val
  ensures pos < 0 || pos >= a.Length  ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  var pos := binarySearch(a, 5);
  assert pos == 2;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0] := 2; a[1] := 4; a[2] := 6; a[3] := 8;
  var pos := binarySearch(a, 3);
  assert pos < 0 || pos >= a.Length;
}
