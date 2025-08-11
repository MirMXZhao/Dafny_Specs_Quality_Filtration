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
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  var index := BinarySearch(a, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0] := 2; a[1] := 4; a[2] := 6; a[3] := 8;
  var index := BinarySearch(a, 3);
  assert index == -1;
}
