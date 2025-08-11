method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{}

////////TESTS////////

method TestMaxArray1() {
  var a := new int[4] [3, 1, 4, 2];
  var max := MaxArray(a);
  assert max == 4;
}

method TestMaxArray2() {
  var a := new int[3] [-5, -2, -8];
  var max := MaxArray(a);
  assert max == -2;
}
