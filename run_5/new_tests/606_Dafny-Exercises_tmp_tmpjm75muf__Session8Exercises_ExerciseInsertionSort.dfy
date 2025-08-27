predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j+1 <= a.Length
reads a
{}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

////////TESTS////////

method TestInsertionSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  var old_multiset := multiset(a[..]);
  InsertionSort(a);
  assert sorted_seg(a, 0, a.Length-1);
  assert multiset(a[..]) == old_multiset;
}

method TestInsertionSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  var old_multiset := multiset(a[..]);
  InsertionSort(a);
  assert sorted_seg(a, 0, a.Length-1);
  assert multiset(a[..]) == old_multiset;
}
