method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{}

function Min(a: seq<int>) : int
    requires |a| > 0
{}

function Max(a: seq<int>) : int
    requires |a| > 0
{}

////////TESTS////////

method TestSumMinMax1() {
  var a := new int[4] [3, 1, 7, 2];
  var sum := SumMinMax(a);
  assert sum == 8;
}

method TestSumMinMax2() {
  var a := new int[5] [-2, 5, -1, 3, 0];
  var sum := SumMinMax(a);
  assert sum == 3;
}
