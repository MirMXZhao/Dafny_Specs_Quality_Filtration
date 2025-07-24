// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{}

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{}

// Simple test case to check the postcondition
method testInsertionSort() {}



method TestInsertionSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  insertionSort(a);
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 4;
}

method TestInsertionSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  insertionSort(a);
  assert a[0] == 5 && a[1] == 5 && a[2] == 5;
}
