method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{}

////////TESTS////////

method TestBubbleSort1() {
  var A := new int[4];
  A[0], A[1], A[2], A[3] := 3, 1, 4, 2;
  BubbleSort(A, 4);
  assert A[0] == 1 && A[1] == 2 && A[2] == 3 && A[3] == 4;
}

method TestBubbleSort2() {
  var A := new int[3];
  A[0], A[1], A[2] := 5, 5, 5;
  BubbleSort(A, 3);
  assert A[0] == 5 && A[1] == 5 && A[2] == 5;
}
