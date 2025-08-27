method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
requires n>=0;            
ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];

{}

////////TESTS////////

method TestSort1() {
  var A := new int[4];
  A[0], A[1], A[2], A[3] := 3, 1, 4, 2;
  sort(A, 4);
  assert A[0] == 1 && A[1] == 2 && A[2] == 3 && A[3] == 4;
}

method TestSort2() {
  var A := new int[3];
  A[0], A[1], A[2] := 5, 5, 5;
  sort(A, 3);
  assert A[0] == 5 && A[1] == 5 && A[2] == 5;
}
