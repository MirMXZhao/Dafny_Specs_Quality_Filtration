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

method testswap1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 10;
  a[2] := 15;
  swap(a, 0, 2);
  assert a[0] == 15;
  assert a[1] == 10;
  assert a[2] == 5;
}

method testswap2() {
  var a := new char[4];
  a[0] := 'a';
  a[1] := 'b';
  a[2] := 'c';
  a[3] := 'd';
  swap(a, 1, 3);
  assert a[0] == 'a';
  assert a[1] == 'd';
  assert a[2] == 'c';
  assert a[3] == 'b';
}

method testswap3() {
  var a := new int[2];
  a[0] := 100;
  a[1] := 200;
  swap(a, 0, 1);
  assert a[0] == 200;
  assert a[1] == 100;
}

method testtwo_way_sort1() {
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

method testtwo_way_sort2() {
  var a := new bool[3];
  a[0] := false;
  a[1] := true;
  a[2] := false;
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == true;
}

method testtwo_way_sort3() {
  var a := new bool[1];
  a[0] := true;
  two_way_sort(a);
  assert a[0] == true;
}
