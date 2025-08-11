method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
{}

////////TESTS////////

method TestElementWiseModulo1() {
  var a := new int[4];
  a[0] := 10; a[1] := 15; a[2] := 8; a[3] := 7;
  var b := new int[4];
  b[0] := 3; b[1] := 4; b[2] := 5; b[3] := 2;
  var result := ElementWiseModulo(a, b);
  assert result[0] == 1;
  assert result[1] == 3;
  assert result[2] == 3;
  assert result[3] == 1;
}

method TestElementWiseModulo2() {
  var a := new int[3];
  a[0] := 20; a[1] := -7; a[2] := 13;
  var b := new int[3];
  b[0] := 6; b[1] := 3; b[2] := 4;
  var result := ElementWiseModulo(a, b);
  assert result[0] == 2;
  assert result[1] == -1;
  assert result[2] == 1;
}
