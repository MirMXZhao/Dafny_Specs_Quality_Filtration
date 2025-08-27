method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{}

predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{}

////////TESTS////////

method TestInsertionSort1() {
  var a := new int[4] := [3, 1, 4, 2];
  var original := multiset(a[..]);
  insertionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == original;
}

method TestInsertionSort2() {
  var a := new int[5] := [5, 2, 8, 1, 9];
  var original := multiset(a[..]);
  insertionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == original;
}
