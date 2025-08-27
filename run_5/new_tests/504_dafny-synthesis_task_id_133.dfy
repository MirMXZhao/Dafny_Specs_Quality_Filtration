function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{}

method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
{}

////////TESTS////////

method TestSumOfNegatives1() {
  var a := new int[4] := [3, -2, 5, -7];
  var result := SumOfNegatives(a);
  assert result == -9;
}

method TestSumOfNegatives2() {
  var a := new int[3] := [1, 2, 3];
  var result := SumOfNegatives(a);
  assert result == 0;
}
