method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
requires X.Length>=1 && n == X.Length;
ensures b>=n;
ensures forall x:: 0<=x<a<n ==> X[x] <= p;
ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
ensures multiset(X[..])==multiset(old(X[..]))
{}