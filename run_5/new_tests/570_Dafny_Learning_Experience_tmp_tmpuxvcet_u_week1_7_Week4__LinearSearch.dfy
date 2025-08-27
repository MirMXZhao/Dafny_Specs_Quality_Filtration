method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
{}

predicate P(n: int) {
    n % 2 == 0
}

method LinearSeach1<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{}

////////TESTS////////

method TestLinearSeach01() {
  var a := new int[4];
  a[0] := 1; a[1] := 3; a[2] := 4; a[3] := 7;
  var n := LinearSeach0(a, P);
  assert n == 2;
}

method TestLinearSeach02() {
  var a := new int[3];
  a[0] := 1; a[1] := 3; a[2] := 5;
  var n := LinearSeach0(a, P);
  assert n == 3;
}

method TestLinearSeach11() {
  var a := new int[4];
  a[0] := 1; a[1] := 3; a[2] := 6; a[3] := 7;
  var n := LinearSeach1(a, P);
  assert n == 2;
}

method TestLinearSeach12() {
  var a := new int[3];
  a[0] := 1; a[1] := 3; a[2] := 5;
  var n := LinearSeach1(a, P);
  assert n == 3;
}
