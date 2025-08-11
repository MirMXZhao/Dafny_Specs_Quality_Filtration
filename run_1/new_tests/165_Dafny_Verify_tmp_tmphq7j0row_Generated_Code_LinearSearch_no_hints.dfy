method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures forall i :: 0 <= i < n ==> !P(a[i])
{}

////////TESTS////////

method TestLinearSearch1() {
  var a := new int[4] := [1, 3, 5, 7];
  var n := LinearSearch(a, x => x > 4);
  assert n == 2;
}

method TestLinearSearch2() {
  var a := new int[3] := [2, 4, 6];
  var n := LinearSearch(a, x => x > 10);
  assert n == 3;
}
