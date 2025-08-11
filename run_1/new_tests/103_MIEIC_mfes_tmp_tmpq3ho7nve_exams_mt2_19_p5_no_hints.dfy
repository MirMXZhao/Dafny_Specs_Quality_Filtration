type T = int

method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{}

////////TESTS////////

method TestPartition1() {
  var a := new T[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 1, 4, 1, 5;
  var pivotPos := partition(a);
  assert pivotPos == 2;
  assert a[..] == [1, 1, 3, 4, 5];
}

method TestPartition2() {
  var a := new T[3];
  a[0], a[1], a[2] := 7, 2, 9;
  var pivotPos := partition(a);
  assert pivotPos == 1;
  assert a[..] == [2, 7, 9];
}
