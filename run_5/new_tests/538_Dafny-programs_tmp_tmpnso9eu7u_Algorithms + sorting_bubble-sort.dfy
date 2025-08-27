predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{}

////////TESTS////////

method TestBubbleSort1() {
  var A := new int[4];
  A[0] := 3; A[1] := 1; A[2] := 4; A[3] := 2;
  var original := multiset(A[..]);
  BubbleSort(A);
  assert sorted(A);
  assert multiset(A[..]) == original;
}

method TestBubbleSort2() {
  var A := new int[3];
  A[0] := 5; A[1] := 5; A[2] := 5;
  var original := multiset(A[..]);
  BubbleSort(A);
  assert sorted(A);
  assert multiset(A[..]) == original;
}
