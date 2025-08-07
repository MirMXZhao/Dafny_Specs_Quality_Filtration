method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{}

////////TESTS////////

method testappendArray1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[2];
  b[0] := 4; b[1] := 5;
  var c := appendArray(a, b);
  assert c.Length == 5;
  assert c[0] == 1 && c[1] == 2 && c[2] == 3 && c[3] == 4 && c[4] == 5;
}

method testappendArray2() {
  var a := new int[0];
  var b := new int[3];
  b[0] := 7; b[1] := 8; b[2] := 9;
  var c := appendArray(a, b);
  assert c.Length == 3;
  assert c[0] == 7 && c[1] == 8 && c[2] == 9;
}

method testappendArray3() {
  var a := new int[2];
  a[0] := 10; a[1] := 20;
  var b := new int[0];
  var c := appendArray(a, b);
  assert c.Length == 2;
  assert c[0] == 10 && c[1] == 20;
}
