method ToArray<T>(xs: seq<T>) returns (a: array<T>)
  ensures fresh(a)
  ensures a.Length == |xs|
  ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
{}

////////TESTS////////

method TestToArray1() {
  var xs := [1, 2, 3, 4];
  var a := ToArray(xs);
  assert a.Length == 4;
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
  assert a[3] == 4;
}

method TestToArray2() {
  var xs := ["hello", "world"];
  var a := ToArray(xs);
  assert a.Length == 2;
  assert a[0] == "hello";
  assert a[1] == "world";
}
