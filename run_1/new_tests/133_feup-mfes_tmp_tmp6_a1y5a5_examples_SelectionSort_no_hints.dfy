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

method TestFindMin1() {
  var a := new real[4];
  a[0] := 3.5; a[1] := 1.2; a[2] := 4.8; a[3] := 2.1;
  var index := findMin(a, 0, 4);
  assert index == 1;
}

method TestFindMin2() {
  var a := new real[3];
  a[0] := 5.0; a[1] := 7.3; a[2] := 6.1;
  var index := findMin(a, 1, 3);
  assert index == 2;
}
