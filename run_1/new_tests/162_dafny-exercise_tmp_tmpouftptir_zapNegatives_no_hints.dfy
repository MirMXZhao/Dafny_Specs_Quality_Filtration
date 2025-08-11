method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
											else a[i] == old(a[i])
ensures a.Length == old(a).Length
{}

////////TESTS////////

method TestZapNegatives1() {
  var a := new int[5];
  a[0] := 3;
  a[1] := -2;
  a[2] := 0;
  a[3] := -5;
  a[4] := 7;
  ZapNegatives(a);
  assert a[0] == 3;
  assert a[1] == 0;
  assert a[2] == 0;
  assert a[3] == 0;
  assert a[4] == 7;
  assert a.Length == 5;
}

method TestZapNegatives2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  ZapNegatives(a);
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
  assert a.Length == 3;
}
