method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{}

////////TESTS////////

method TestBubbleSort1() {
  var a := new int[4] [3, 1, 4, 2];
  BubbleSort(a);
  assert a[..] == [1, 2, 3, 4];
}

method TestBubbleSort2() {
  var a := new int[3] [5, 5, 5];
  BubbleSort(a);
  assert a[..] == [5, 5, 5];
}
