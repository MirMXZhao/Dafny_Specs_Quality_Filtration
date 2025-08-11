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

////////TESTS////////

method TestAdditiveFactorial1() {
  var u := AdditiveFactorial(5);
  assert u == Factorial(5);
}

method TestAdditiveFactorial2() {
  var u := AdditiveFactorial(0);
  assert u == Factorial(0);
}

method TestFIND1() {
  var A := new int[5];
  A[0] := 3; A[1] := 1; A[2] := 4; A[3] := 1; A[4] := 5;
  FIND(A, 5, 2);
  assert forall p,q :: 0 <= p <= 2 <= q < 5 ==> A[p] <= A[q];
}

method TestFIND2() {
  var A := new int[3];
  A[0] := 7; A[1] := 2; A[2] := 9;
  FIND(A, 3, 1);
  assert forall p,q :: 0 <= p <= 1 <= q < 3 ==> A[p] <= A[q];
}
