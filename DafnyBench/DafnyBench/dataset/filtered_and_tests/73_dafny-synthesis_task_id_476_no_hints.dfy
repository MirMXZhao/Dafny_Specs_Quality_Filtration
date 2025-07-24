method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{}

function Max(a: seq<int>) : int
    requires |a| > 0
{}

method TestSumMinMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 1;
  a[2] := 7;
  a[3] := 2;
  var sum := SumMinMax(a);
  assert sum == 8;
}

method TestSumMinMax2() {
  var a := new int[3];
  a[0] := -5;
  a[1] := 10;
  a[2] := 3;
  var sum := SumMinMax(a);
  assert sum == 5;
}
