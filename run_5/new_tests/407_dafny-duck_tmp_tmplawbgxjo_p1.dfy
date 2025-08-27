function Sum(xs: seq<int>): int {}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{}

////////TESTS////////

method TestSum1() {
  var xs := [1, 2, 3, 4];
  var result := Sum(xs);
  assert result == 10;
}

method TestSum2() {
  var xs := [];
  var result := Sum(xs);
  assert result == 0;
}

method TestSumArray1() {
  var xs := new int[4];
  xs[0] := 1; xs[1] := 2; xs[2] := 3; xs[3] := 4;
  var s := SumArray(xs);
  assert s == 10;
}

method TestSumArray2() {
  var xs := new int[0];
  var s := SumArray(xs);
  assert s == 0;
}
