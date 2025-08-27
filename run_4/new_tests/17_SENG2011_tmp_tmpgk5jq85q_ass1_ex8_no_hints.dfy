method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}

////////TESTS////////

method TestGetEven1() {
  var a := new nat[4] := [1, 3, 5, 7];
  GetEven(a);
  assert a[0] % 2 == 0;
  assert a[1] % 2 == 0;
  assert a[2] % 2 == 0;
  assert a[3] % 2 == 0;
}

method TestGetEven2() {
  var a := new nat[3] := [2, 8, 12];
  GetEven(a);
  assert a[0] % 2 == 0;
  assert a[1] % 2 == 0;
  assert a[2] % 2 == 0;
}
