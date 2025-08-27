method addArrays(a : array<int>, b : array<int>) returns (c : array<int>) 
requires a.Length == b.Length
ensures b.Length == c.Length
ensures forall i:int :: 0 <= i <c.Length ==> c[i] == a[i] + b[i]

{}

////////TESTS////////

method TestAddArrays1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[3];
  b[0] := 4; b[1] := 5; b[2] := 6;
  var c := addArrays(a, b);
  assert c[0] == 5;
  assert c[1] == 7;
  assert c[2] == 9;
}

method TestAddArrays2() {
  var a := new int[2];
  a[0] := -1; a[1] := 10;
  var b := new int[2];
  b[0] := 3; b[1] := -5;
  var c := addArrays(a, b);
  assert c[0] == 2;
  assert c[1] == 5;
}
