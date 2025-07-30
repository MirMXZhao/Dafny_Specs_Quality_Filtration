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

method testinsertionSort1() {
  var a := new int[4] := [3, 1, 4, 2];
  var oldMultiset := multiset(a[..]);
  insertionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == oldMultiset;
}

method testinsertionSort2() {
  var a := new int[3] := [5, 5, 5];
  var oldMultiset := multiset(a[..]);
  insertionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == oldMultiset;
}

method testinsertionSort3() {
  var a := new int[0];
  var oldMultiset := multiset(a[..]);
  insertionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == oldMultiset;
}

method testisSorted1() {
  var a := new int[4] := [1, 2, 3, 4];
  var result := isSorted(a, 0, 4);
  assert result == true;
}

method testisSorted2() {
  var a := new int[3] := [3, 1, 2];
  var result := isSorted(a, 0, 3);
  assert result == false;
}
