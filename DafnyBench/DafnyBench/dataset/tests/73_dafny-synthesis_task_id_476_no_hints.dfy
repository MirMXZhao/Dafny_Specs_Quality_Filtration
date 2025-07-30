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
  var a := new int[3];
  a[0] := 1;
  a[1] := 5;
  a[2] := 3;
  var sum := SumMinMax(a);
  assert sum == 6;
}

method TestSumMinMax2() {
  var a := new int[4];
  a[0] := -2;
  a[1] := 0;
  a[2] := 7;
  a[3] := 1;
  var sum := SumMinMax(a);
  assert sum == 5;
}

method TestSumMinMax3() {
  var a := new int[1];
  a[0] := 42;
  var sum := SumMinMax(a);
  assert sum == 84;
}
