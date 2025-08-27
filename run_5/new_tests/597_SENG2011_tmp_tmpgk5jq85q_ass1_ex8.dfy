method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}

////////TESTS////////

method TestGetEven1() {
  var a := new nat[4];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7;
  GetEven(a);
  assert forall i :: 0 <= i < a.Length ==> a[i] % 2 == 0;
}

method TestGetEven2() {
  var a := new nat[3];
  a[0] := 10; a[1] := 15; a[2] := 20;
  GetEven(a);
  assert forall i :: 0 <= i < a.Length ==> a[i] % 2 == 0;
}
