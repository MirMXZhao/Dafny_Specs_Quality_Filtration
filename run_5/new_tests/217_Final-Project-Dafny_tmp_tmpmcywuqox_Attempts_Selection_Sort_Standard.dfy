method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{}

////////TESTS////////

method TestSelectionSorted1() {
  var arr := new int[4] [3, 1, 4, 2];
  selectionSorted(arr);
  assert multiset(arr[..]) == multiset([3, 1, 4, 2]);
}

method TestSelectionSorted2() {
  var arr := new int[5] [5, 2, 8, 1, 9];
  selectionSorted(arr);
  assert multiset(arr[..]) == multiset([5, 2, 8, 1, 9]);
}
