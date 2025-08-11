method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

////////TESTS////////

method TestReverse1() {
  var a := new int[4] := [1, 2, 3, 4];
  reverse(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestReverse2() {
  var a := new int[3] := [5, 10, 15];
  reverse(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}
