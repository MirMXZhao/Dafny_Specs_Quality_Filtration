predicate sorted(a: array?<int>, l: int, u: int)
	reads a
	requires a != null
	{}

method BinarySearch(a: array?<int>, key: int)
	returns (index: int)
	requires a != null && sorted(a,0,a.Length-1);
	ensures index >= 0 ==> index < a.Length && a[index] == key;
	ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
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
  assert index < 0;
}
