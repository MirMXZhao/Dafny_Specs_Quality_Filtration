method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{}

////////TESTS////////

method TestMaxDifference1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 5;
  a[2] := 3;
  a[3] := 9;
  var diff := MaxDifference(a);
  assert diff == 8;
}

method TestMaxDifference2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 2;
  a[2] := 7;
  var diff := MaxDifference(a);
  assert diff == 8;
}
