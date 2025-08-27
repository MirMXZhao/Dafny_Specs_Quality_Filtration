method arrayProduct(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] * b[i]==c[i]
{}

////////TESTS////////

method TestArrayProduct1() {
  var a := new int[3];
  a[0] := 2; a[1] := 3; a[2] := 4;
  var b := new int[3];
  b[0] := 1; b[1] := 2; b[2] := 3;
  var c := arrayProduct(a, b);
  assert c[0] == 2;
  assert c[1] == 6;
  assert c[2] == 12;
}

method TestArrayProduct2() {
  var a := new int[2];
  a[0] := -1; a[1] := 5;
  var b := new int[2];
  b[0] := 3; b[1] := -2;
  var c := arrayProduct(a, b);
  assert c[0] == -3;
  assert c[1] == -10;
}
