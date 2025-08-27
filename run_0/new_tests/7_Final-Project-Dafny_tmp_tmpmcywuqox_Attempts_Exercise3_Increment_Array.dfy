method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}

////////TESTS////////

method TestIncrementArray1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  incrementArray(a);
  assert a[0] == 2 && a[1] == 3 && a[2] == 4;
}

method TestIncrementArray2() {
  var a := new int[1];
  a[0] := -5;
  incrementArray(a);
  assert a[0] == -4;
}
