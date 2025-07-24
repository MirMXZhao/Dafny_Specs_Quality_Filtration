method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{}



method TestAppendArray1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var b := new int[2];
  b[0], b[1] := 4, 5;
  var c := appendArray(a, b);
  assert c[0] == 1 && c[1] == 2 && c[2] == 3 && c[3] == 4 && c[4] == 5;
}

method TestAppendArray2() {
  var a := new int[0];
  var b := new int[3];
  b[0], b[1], b[2] := 7, 8, 9;
  var c := appendArray(a, b);
  assert c[0] == 7 && c[1] == 8 && c[2] == 9;
}
