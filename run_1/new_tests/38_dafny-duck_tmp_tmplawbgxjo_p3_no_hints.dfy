method max(x:array<nat>) returns (y:nat) 
requires x.Length > 0
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
ensures y in x[..]
{}

////////TESTS////////

method TestMax1() {
  var x := new nat[3];
  x[0] := 5;
  x[1] := 2;
  x[2] := 8;
  var y := max(x);
  assert y == 8;
}

method TestMax2() {
  var x := new nat[4];
  x[0] := 1;
  x[1] := 1;
  x[2] := 1;
  x[3] := 1;
  var y := max(x);
  assert y == 1;
}
