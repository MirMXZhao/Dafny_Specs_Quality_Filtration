method LinearSearch(a: array<int>, e: int) returns (n:int)
  requires exists i::0<=i<a.Length && a[i]==e
  ensures 0<=n<a.Length && a[n]==e
  ensures forall k :: 0 <= k < n ==> a[k]!=e
{}

////////TESTS////////

method TestLinearSearch1() {
  var a := new int[4] [3, 1, 4, 1];
  var n := LinearSearch(a, 1);
  assert n == 1;
}

method TestLinearSearch2() {
  var a := new int[5] [7, 2, 9, 2, 5];
  var n := LinearSearch(a, 2);
  assert n == 1;
}
