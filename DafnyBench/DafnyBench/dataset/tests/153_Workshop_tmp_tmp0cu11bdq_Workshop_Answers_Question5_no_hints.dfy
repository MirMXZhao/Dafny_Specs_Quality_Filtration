method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{}

////////TESTS////////

method testrev1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var old_a := a[..];
  rev(a);
  assert a[0] == old_a[3];
  assert a[1] == old_a[2];
  assert a[2] == old_a[1];
  assert a[3] == old_a[0];
}

method testrev2() {
  var a := new int[3];
  a[0] := 5; a[1] := 10; a[2] := 15;
  var old_a := a[..];
  rev(a);
  assert a[0] == old_a[2];
  assert a[1] == old_a[1];
  assert a[2] == old_a[0];
}

method testrev3() {
  var a := new int[0];
  var old_a := a[..];
  rev(a);
  assert a[..] == old_a;
}
