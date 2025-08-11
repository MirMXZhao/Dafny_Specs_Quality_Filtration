method FindMax(a: array<int>) returns (i: int)
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 7, 2, 9;
  var i := FindMax(a);
  assert i == 3;
}

method TestFindMax2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 1;
  var i := FindMax(a);
  assert i == 0 || i == 1;
}
