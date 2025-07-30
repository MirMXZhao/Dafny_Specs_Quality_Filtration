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
  a[0] := 1;
  a[1] := 4;
  a[2] := 2;
  a[3] := 3;
  var result := PairwiseAddition(a);
  assert result.Length == 2;
  assert result[0] == 5;
  assert result[1] == 5;
}

method TestPairwiseAddition2() {
  var a := new int[6];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  a[3] := 40;
  a[4] := 50;
  a[5] := 60;
  var result := PairwiseAddition(a);
  assert result.Length == 3;
  assert result[0] == 30;
  assert result[1] == 70;
  assert result[2] == 110;
}

method TestPairwiseAddition3() {
  var a := new int[2];
  a[0] := -5;
  a[1] := 3;
  var result := PairwiseAddition(a);
  assert result.Length == 1;
  assert result[0] == -2;
}

method TestPairwiseAddition4() {
  var a := new int[0];
  var result := PairwiseAddition(a);
  assert result.Length == 0;
}
