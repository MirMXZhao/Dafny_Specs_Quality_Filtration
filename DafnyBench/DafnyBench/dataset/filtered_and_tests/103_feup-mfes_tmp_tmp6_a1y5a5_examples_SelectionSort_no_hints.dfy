/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{}

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{}

method testSelectionSort() {}

method testFindMin() {}


method testSelectionSort() {
  var a := new real[4];
  a[0] := 3.0; a[1] := 1.0; a[2] := 4.0; a[3] := 2.0;
  selectionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == multiset([3.0, 1.0, 4.0, 2.0]);
}

method testFindMin() {
  var a := new real[3];
  a[0] := 5.0; a[1] := 2.0; a[2] := 8.0;
  var index := findMin(a, 0, 3);
  assert 0 <= index < 3;
  assert forall k :: 0 <= k < 3 ==> a[k] >= a[index];
}
