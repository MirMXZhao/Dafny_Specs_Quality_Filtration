method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
requires X.Length>=1 && n == X.Length;
ensures b>=n;
ensures forall x:: 0<=x<a<n ==> X[x] <= p;
ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
ensures multiset(X[..])==multiset(old(X[..]))
{}

////////TESTS////////

method TestQuicksortPartition1() {
  var X := new int[5];
  X[0], X[1], X[2], X[3], X[4] := 3, 1, 4, 2, 5;
  var a, b := QuicksortPartition(X, 5, 3);
  assert a <= 5;
  assert b >= 5;
  assert forall x :: 0 <= x < a ==> X[x] <= 3;
  assert a == 5 || forall x :: a <= x < 5 ==> X[x] > 3;
}

method TestQuicksortPartition2() {
  var X := new int[3];
  X[0], X[1], X[2] := 7, 8, 9;
  var a, b := QuicksortPartition(X, 3, 5);
  assert a <= 3;
  assert b >= 3;
  assert forall x :: 0 <= x < a ==> X[x] <= 5;
  assert a == 3 || forall x :: a <= x < 3 ==> X[x] > 5;
}
