method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{}


method TestRev1() {
  var a := new int[4] [1, 2, 3, 4];
  rev(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestRev2() {
  var a := new int[3] [10, 20, 30];
  rev(a);
  assert a[0] == 30 && a[1] == 20 && a[2] == 10;
}
