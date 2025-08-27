method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
{}

////////TESTS////////

method TestPairwiseAddition1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var result := PairwiseAddition(a);
  assert result[0] == 3;
  assert result[1] == 7;
}

method TestPairwiseAddition2() {
  var a := new int[6];
  a[0] := 5; a[1] := -2; a[2] := 0; a[3] := 8; a[4] := -1; a[5] := 3;
  var result := PairwiseAddition(a);
  assert result[0] == 3;
  assert result[1] == 8;
  assert result[2] == 2;
}
