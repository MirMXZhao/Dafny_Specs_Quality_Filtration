method ElementWiseSubtraction(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] - b[i]
{}

////////TESTS////////

method TestElementWiseSubtraction1() {
  var a := new int[4];
  a[0] := 5; a[1] := 8; a[2] := 3; a[3] := 7;
  var b := new int[4];
  b[0] := 2; b[1] := 4; b[2] := 1; b[3] := 6;
  var result := ElementWiseSubtraction(a, b);
  assert result[0] == 3;
  assert result[1] == 4;
  assert result[2] == 2;
  assert result[3] == 1;
}

method TestElementWiseSubtraction2() {
  var a := new int[3];
  a[0] := 10; a[1] := -5; a[2] := 0;
  var b := new int[3];
  b[0] := 3; b[1] := -2; b[2] := 8;
  var result := ElementWiseSubtraction(a, b);
  assert result[0] == 7;
  assert result[1] == -3;
  assert result[2] == -8;
}
