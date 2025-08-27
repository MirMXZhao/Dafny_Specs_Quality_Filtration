method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{}

////////TESTS////////

method TestMinArray1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  var r := minArray(a);
  assert r == 1;
}

method TestMinArray2() {
  var a := new int[3];
  a[0], a[1], a[2] := -5, -2, -8;
  var r := minArray(a);
  assert r == -8;
}
