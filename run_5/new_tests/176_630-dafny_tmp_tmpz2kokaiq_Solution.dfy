function sorted(a: array<int>) : bool
    reads a
{}

method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 3, 5, 7;
  var index := BinarySearch(a, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var a := new int[3];
  a[0], a[1], a[2] := 2, 4, 6;
  var index := BinarySearch(a, 3);
  assert index == -1;
}
