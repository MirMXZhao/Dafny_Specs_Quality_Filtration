// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{}

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{}



method TestFactorial1() {
  var u := AdditiveFactorial(0);
  assert u == Factorial(0);
}

method TestFactorial2() {
  var u := AdditiveFactorial(5);
  assert u == Factorial(5);
}

method TestFIND1() {
  var A := new int[5];
  A[0], A[1], A[2], A[3], A[4] := 3, 1, 4, 1, 5;
  FIND(A, 5, 2);
  assert forall p,q :: 0 <= p <= 2 <= q < 5 ==> A[p] <= A[q];
}

method TestFIND2() {
  var A := new int[3];
  A[0], A[1], A[2] := 10, 5, 15;
  FIND(A, 3, 1);
  assert forall p,q :: 0 <= p <= 1 <= q < 3 ==> A[p] <= A[q];
}
