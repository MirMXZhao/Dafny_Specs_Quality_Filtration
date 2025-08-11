method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k :: 0 <= k < a.Length && max == a[k]
  ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{}

////////TESTS////////

method TestFindMax1() {
  var a := new real[4];
  a[0] := 3.5;
  a[1] := 1.2;
  a[2] := 7.8;
  a[3] := 2.1;
  var max := findMax(a);
  assert max == 7.8;
}

method TestFindMax2() {
  var a := new real[3];
  a[0] := -2.5;
  a[1] := -8.1;
  a[2] := -1.0;
  var max := findMax(a);
  assert max == -1.0;
}
