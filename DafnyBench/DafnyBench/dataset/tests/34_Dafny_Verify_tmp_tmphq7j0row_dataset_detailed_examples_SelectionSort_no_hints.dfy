method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

////////TESTS////////

method TestSelectionSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 64, 34, 25, 12;
  SelectionSort(a);
  assert a[0] == 12 && a[1] == 25 && a[2] == 34 && a[3] == 64;
}

method TestSelectionSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 2, 8;
  SelectionSort(a);
  assert a[0] == 2 && a[1] == 5 && a[2] == 8;
}

method TestSelectionSort3() {
  var a := new int[1];
  a[0] := 42;
  SelectionSort(a);
  assert a[0] == 42;
}
