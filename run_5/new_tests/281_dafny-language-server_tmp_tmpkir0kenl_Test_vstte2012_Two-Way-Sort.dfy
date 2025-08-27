method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

////////TESTS////////

method TestSwap1() {
  var a := new int[4] [1, 2, 3, 4];
  swap(a, 0, 2);
  assert a[0] == 3;
  assert a[2] == 1;
  assert a[1] == 2;
  assert a[3] == 4;
}

method TestSwap2() {
  var a := new char[3] ['a', 'b', 'c'];
  swap(a, 1, 2);
  assert a[1] == 'c';
  assert a[2] == 'b';
  assert a[0] == 'a';
}

method TestTwoWaySort1() {
  var a := new bool[4] [true, false, true, false];
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == true;
  assert a[3] == true;
}

method TestTwoWaySort2() {
  var a := new bool[3] [true, true, false];
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == true;
  assert a[2] == true;
}
