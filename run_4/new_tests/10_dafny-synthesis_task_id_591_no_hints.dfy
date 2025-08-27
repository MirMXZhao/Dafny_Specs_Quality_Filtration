method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}

////////TESTS////////

method TestSwapFirstAndLast1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  SwapFirstAndLast(a);
  assert a[0] == 4 && a[1] == 2 && a[2] == 3 && a[3] == 1;
}

method TestSwapFirstAndLast2() {
  var a := new int[1];
  a[0] := 5;
  SwapFirstAndLast(a);
  assert a[0] == 5;
}
