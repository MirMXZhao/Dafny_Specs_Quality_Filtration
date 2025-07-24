method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
{}



method TestFindMax1() {
  var a := new int[4];
  a[0] := 3; a[1] := 7; a[2] := 2; a[3] := 9;
  var max := FindMax(a);
  assert max == 3;
}

method TestFindMax2() {
  var a := new int[3];
  a[0] := 5; a[1] := 1; a[2] := 5;
  var max := FindMax(a);
  assert max == 0 || max == 2;
}
