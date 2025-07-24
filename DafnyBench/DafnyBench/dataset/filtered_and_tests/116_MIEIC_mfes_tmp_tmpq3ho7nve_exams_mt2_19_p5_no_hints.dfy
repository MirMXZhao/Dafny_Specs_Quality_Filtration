type T = int // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{}


method TestPartition1() {
  var a := new T[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 1, 4, 1, 5;
  var pivotPos := partition(a);
  assert 0 <= pivotPos < 5;
  assert forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos];
  assert forall i :: pivotPos < i < 5 ==> a[i] >= a[pivotPos];
}

method TestPartition2() {
  var a := new T[3];
  a[0], a[1], a[2] := 7, 2, 9;
  var pivotPos := partition(a);
  assert 0 <= pivotPos < 3;
  assert forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos];
  assert forall i :: pivotPos < i < 3 ==> a[i] >= a[pivotPos];
}
