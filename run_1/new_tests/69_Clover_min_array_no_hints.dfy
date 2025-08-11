method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{}

////////TESTS////////

method TestMinArray1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var r := minArray(a);
  assert r == 1;
}

method TestMinArray2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 10;
  a[2] := 10;
  var r := minArray(a);
  assert r == 10;
}
