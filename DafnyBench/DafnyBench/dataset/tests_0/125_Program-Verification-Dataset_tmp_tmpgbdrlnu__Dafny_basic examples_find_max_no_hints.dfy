method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 1;
  a[3] := 5;
  var max := FindMax(a);
  assert max == 1;
}

method TestFindMax2() {
  var a := new int[3];
  a[0] := 9;
  a[1] := 2;
  a[2] := 9;
  var max := FindMax(a);
  assert max == 0 || max == 2;
}

method TestFindMax3() {
  var a := new int[1];
  a[0] := 42;
  var max := FindMax(a);
  assert max == 0;
}
