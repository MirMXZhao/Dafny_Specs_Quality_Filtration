method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{}

////////TESTS////////

method TestRev1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var old_a := [1, 2, 3, 4];
  rev(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestRev2() {
  var a := new int[3];
  a[0] := 5; a[1] := 10; a[2] := 15;
  var old_a := [5, 10, 15];
  rev(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}
