predicate sorted (a: array<int>)
	requires a != null
	reads a
{}

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{}

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
{}

////////TESTS////////

method TestSelectionSort1() {
  var a := new int[4] [3, 1, 4, 2];
  SelectionSort(a);
  assert sorted(a);
}

method TestSelectionSort2() {
  var a := new int[5] [5, 2, 8, 1, 9];
  SelectionSort(a);
  assert sorted(a);
}
