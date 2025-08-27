method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
											else a[i] == old(a[i])
ensures a.Length == old(a).Length
{}

////////TESTS////////

method TestZapNegatives1() {
  var a := new int[5] [-3, 7, -1, 0, 4];
  ZapNegatives(a);
  assert a[0] == 0;
  assert a[1] == 7;
  assert a[2] == 0;
  assert a[3] == 0;
  assert a[4] == 4;
}

method TestZapNegatives2() {
  var a := new int[4] [1, 2, 3, 4];
  ZapNegatives(a);
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
  assert a[3] == 4;
}
