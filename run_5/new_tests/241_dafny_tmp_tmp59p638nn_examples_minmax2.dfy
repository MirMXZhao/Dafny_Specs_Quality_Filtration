method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{}

////////TESTS////////

method TestDifferenceMinMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 1;
  a[2] := 7;
  a[3] := 2;
  var diff := DifferenceMinMax(a);
  assert diff == 6;
}

method TestDifferenceMinMax2() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 5;
  a[2] := 5;
  var diff := DifferenceMinMax(a);
  assert diff == 0;
}
