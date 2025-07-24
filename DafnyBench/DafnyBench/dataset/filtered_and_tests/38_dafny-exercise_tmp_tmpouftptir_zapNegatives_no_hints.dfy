method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
											else a[i] == old(a[i])
ensures a.Length == old(a).Length
{}

method Main() 
{}



method TestZapNegatives1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, -2, 3, -4, 5;
  ZapNegatives(a);
  assert a[0] == 1;
  assert a[1] == 0;
  assert a[2] == 3;
  assert a[3] == 0;
  assert a[4] == 5;
}

method TestZapNegatives2() {
  var a := new int[3];
  a[0], a[1], a[2] := 10, 20, 30;
  ZapNegatives(a);
  assert a[0] == 10;
  assert a[1] == 20;
  assert a[2] == 30;
}
