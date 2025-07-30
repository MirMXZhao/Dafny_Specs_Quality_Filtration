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
  X[0] := 3; X[1] := 1; X[2] := 4; X[3] := 1; X[4] := 5;
  var a, b := QuicksortPartition(X, 5, 3);
  assert a <= 5;
  assert b >= 5;
}

method TestQuicksortPartition2() {
  var X := new int[3];
  X[0] := 7; X[1] := 2; X[2] := 9;
  var a, b := QuicksortPartition(X, 3, 5);
  assert a <= 3;
  assert b >= 3;
}

method TestQuicksortPartition3() {
  var X := new int[1];
  X[0] := 10;
  var a, b := QuicksortPartition(X, 1, 5);
  assert a <= 1;
  assert b >= 1;
}
