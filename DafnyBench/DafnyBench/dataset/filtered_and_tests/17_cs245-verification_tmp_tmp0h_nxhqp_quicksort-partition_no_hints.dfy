// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...
   
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
{}

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */



method TestQuicksortPartition1() {
  var X := new int[5];
  X[0], X[1], X[2], X[3], X[4] := 3, 1, 4, 1, 5;
  var a, b := QuicksortPartition(X, 5, 2);
  assert a >= 0 && a <= 5;
  assert b >= 5;
}

method TestQuicksortPartition2() {
  var X := new int[3];
  X[0], X[1], X[2] := 7, 8, 9;
  var a, b := QuicksortPartition(X, 3, 10);
  assert a >= 0 && a <= 3;
  assert b >= 3;
}
