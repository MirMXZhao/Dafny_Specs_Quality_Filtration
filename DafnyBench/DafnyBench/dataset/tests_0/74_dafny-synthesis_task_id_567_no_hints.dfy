method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
{}

////////TESTS////////

method TestIsSorted1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 5;
  a[3] := 7;
  var sorted := IsSorted(a);
  assert sorted == true;
}

method TestIsSorted2() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var sorted := IsSorted(a);
  assert sorted == false;
}

method TestIsSorted3() {
  var a := new int[1];
  a[0] := 42;
  var sorted := IsSorted(a);
  assert sorted == true;
}
