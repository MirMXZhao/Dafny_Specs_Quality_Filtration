method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 3, 5, 7, 9;
  var n := BinarySearch(a, 6);
  assert n == 3;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 2, 4, 6, 8;
  var n := BinarySearch(a, 4);
  assert n == 1;
}
