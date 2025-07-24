// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
{}


method TestSelectionSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  SelectionSort(a);
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 4;
}

method TestSelectionSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  SelectionSort(a);
  assert a[0] == 5 && a[1] == 5 && a[2] == 5;
}
