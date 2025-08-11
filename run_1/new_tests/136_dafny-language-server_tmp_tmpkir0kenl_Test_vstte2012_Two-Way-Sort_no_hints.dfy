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
  var a := new int[4];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  a[3] := 40;
  swap(a, 1, 2);
  assert a[0] == 10;
  assert a[1] == 30;
  assert a[2] == 20;
  assert a[3] == 40;
}

method TestSwap2() {
  var a := new char[3];
  a[0] := 'x';
  a[1] := 'y';
  a[2] := 'z';
  swap(a, 0, 2);
  assert a[0] == 'z';
  assert a[1] == 'y';
  assert a[2] == 'x';
}

method TestTwoWaySort1() {
  var a := new bool[4];
  a[0] := true;
  a[1] := false;
  a[2] := true;
  a[3] := false;
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == true;
  assert a[3] == true;
}

method TestTwoWaySort2() {
  var a := new bool[3];
  a[0] := false;
  a[1] := true;
  a[2] := false;
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == true;
}
