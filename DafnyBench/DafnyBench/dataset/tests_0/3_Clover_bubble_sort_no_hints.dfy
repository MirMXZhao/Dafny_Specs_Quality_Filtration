method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{}

////////TESTS////////

method TestBubbleSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  BubbleSort(a);
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 4;
}

method TestBubbleSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  BubbleSort(a);
  assert a[0] == 5 && a[1] == 5 && a[2] == 5;
}

method TestBubbleSort3() {
  var a := new int[0];
  BubbleSort(a);
  assert a.Length == 0;
}
