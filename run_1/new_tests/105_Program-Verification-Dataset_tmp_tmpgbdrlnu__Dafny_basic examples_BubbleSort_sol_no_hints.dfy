predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{}
  
predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{}

method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
{}

////////TESTS////////

method TestBubbleSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  bubbleSort(a);
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 4;
}

method TestBubbleSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 5;
  bubbleSort(a);
  assert a[0] == 5 && a[1] == 5 && a[2] == 5;
}
