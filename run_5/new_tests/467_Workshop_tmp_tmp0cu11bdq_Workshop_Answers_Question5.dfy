method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{}

////////TESTS////////

method testrev1() {
  var a := new int[4] := [1, 2, 3, 4];
  var old_a := a[..];
  rev(a);
  assert a[..] == [4, 3, 2, 1];
}

method testrev2() {
  var a := new int[3] := [5, 10, 15];
  var old_a := a[..];
  rev(a);
  assert a[..] == [15, 10, 5];
}
