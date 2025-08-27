method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures forall i :: 0 <= i < n ==> !P(a[i])
{}

////////TESTS////////

method TestLinearSearch1() {
  var a := new int[4];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  a[3] := 40;
  var n := LinearSearch(a, x => x > 25);
  assert n == 2;
}

method TestLinearSearch2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var n := LinearSearch(a, x => x > 10);
  assert n == 3;
}
