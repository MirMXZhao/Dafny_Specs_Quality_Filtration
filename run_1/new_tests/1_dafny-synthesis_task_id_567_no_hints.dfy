method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
{}

////////TESTS////////

method TestIsSorted1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var sorted := IsSorted(a);
  assert sorted == true;
}

method TestIsSorted2() {
  var a := new int[4];
  a[0] := 3; a[1] := 1; a[2] := 2; a[3] := 4;
  var sorted := IsSorted(a);
  assert sorted == false;
}
