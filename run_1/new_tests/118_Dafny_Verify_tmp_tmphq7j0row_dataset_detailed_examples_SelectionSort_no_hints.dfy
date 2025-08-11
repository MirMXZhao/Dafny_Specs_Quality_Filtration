method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

////////TESTS////////

method TestSelectionSort1() {
  var a := new int[4] := [64, 25, 12, 22];
  SelectionSort(a);
  assert a[..] == [12, 22, 25, 64];
}

method TestSelectionSort2() {
  var a := new int[3] := [3, 1, 2];
  SelectionSort(a);
  assert a[..] == [1, 2, 3];
}
