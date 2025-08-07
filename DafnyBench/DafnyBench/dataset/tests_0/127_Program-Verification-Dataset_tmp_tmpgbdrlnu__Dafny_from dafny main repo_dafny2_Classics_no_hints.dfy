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

method testFactorial1() {
  var u := AdditiveFactorial(0);
  assert u == 1;
}

method testFactorial2() {
  var u := AdditiveFactorial(3);
  assert u == 6;
}

method testFactorial3() {
  var u := AdditiveFactorial(1);
  assert u == 1;
}

method testFIND1() {
  var A := new int[5];
  A[0], A[1], A[2], A[3], A[4] := 5, 2, 8, 1, 9;
  FIND(A, 5, 2);
  assert forall p,q :: 0 <= p <= 2 <= q < 5 ==> A[p] <= A[q];
}

method testFIND2() {
  var A := new int[3];
  A[0], A[1], A[2] := 3, 1, 7;
  FIND(A, 3, 1);
  assert forall p,q :: 0 <= p <= 1 <= q < 3 ==> A[p] <= A[q];
}

method testFIND3() {
  var A := new int[1];
  A[0] := 42;
  FIND(A, 1, 0);
  assert forall p,q :: 0 <= p <= 0 <= q < 1 ==> A[p] <= A[q];
}
