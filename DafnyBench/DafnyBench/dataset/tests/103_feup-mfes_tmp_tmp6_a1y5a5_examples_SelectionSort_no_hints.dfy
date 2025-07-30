predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

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

////////TESTS////////

method testFindMin1() {
  var a := new real[4];
  a[0] := 3.5;
  a[1] := 1.2;
  a[2] := 4.8;
  a[3] := 2.1;
  var index := findMin(a, 0, 4);
  assert index == 1;
}

method testFindMin2() {
  var a := new real[3];
  a[0] := 7.0;
  a[1] := 5.5;
  a[2] := 9.2;
  var index := findMin(a, 1, 3);
  assert index == 1;
}

method testFindMin3() {
  var a := new real[5];
  a[0] := 2.0;
  a[1] := 2.0;
  a[2] := 2.0;
  a[3] := 2.0;
  a[4] := 2.0;
  var index := findMin(a, 2, 4);
  assert index == 2 || index == 3;
}

method testSelectionSort1() {
  var a := new real[4];
  a[0] := 3.5;
  a[1] := 1.2;
  a[2] := 4.8;
  a[3] := 2.1;
  var oldContents := a[..];
  selectionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == multiset(oldContents);
}

method testSelectionSort2() {
  var a := new real[1];
  a[0] := 5.0;
  var oldContents := a[..];
  selectionSort(a);
  assert isSorted(a, 0, a.Length);
  assert multiset(a[..]) == multiset(oldContents);
}
