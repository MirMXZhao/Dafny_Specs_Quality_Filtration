predicate sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {}
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {}

method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  {}

////////TESTS////////

method TestBubbleSort1() {
  var a := new int[4];
  a[0] := 4; a[1] := 2; a[2] := 7; a[3] := 1;
  BubbleSort(a);
  assert a[0] == 1 && a[1] == 2 && a[2] == 4 && a[3] == 7;
}

method TestBubbleSort2() {
  var a := new int[3];
  a[0] := 5; a[1] := 5; a[2] := 5;
  BubbleSort(a);
  assert a[0] == 5 && a[1] == 5 && a[2] == 5;
}
