ghost function Factorial(n: nat): nat
{}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{}

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{}