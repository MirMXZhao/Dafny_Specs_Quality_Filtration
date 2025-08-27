function abs(a:int):nat
{}

method aba(a:array<int>)returns (b:array<int>)
ensures a.Length == b.Length
ensures forall x :: 0<=x<b.Length ==> b[x] == abs(a[x])
{}

////////TESTS////////

method testaba1() {
  var a := new int[3];
  a[0] := -5;
  a[1] := 3;
  a[2] := -2;
  var b := aba(a);
  assert b[0] == 5;
  assert b[1] == 3;
  assert b[2] == 2;
}

method testaba2() {
  var a := new int[4];
  a[0] := 0;
  a[1] := -7;
  a[2] := 10;
  a[3] := -1;
  var b := aba(a);
  assert b[0] == 0;
  assert b[1] == 7;
  assert b[2] == 10;
  assert b[3] == 1;
}
