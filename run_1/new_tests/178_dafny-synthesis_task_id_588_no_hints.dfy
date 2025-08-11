method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
{}

function Min(a: seq<int>) : int
    requires |a| > 0
{}

function Max(a: seq<int>) : int
    requires |a| > 0
{}

////////TESTS////////

method TestDifferenceMinMax1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 1, 7, 2, 9;
  var diff := DifferenceMinMax(a);
  assert diff == 8;
}

method TestDifferenceMinMax2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  var diff := DifferenceMinMax(a);
  assert diff == 0;
}
