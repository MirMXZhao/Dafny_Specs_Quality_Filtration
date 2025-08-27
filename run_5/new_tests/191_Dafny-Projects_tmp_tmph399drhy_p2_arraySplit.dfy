method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{}

////////TESTS////////

method TestArraySplit1() {
  var a := new int[4] [1, 2, 3, 4];
  var b, c := ArraySplit(a);
  assert b[..] == [1, 2];
  assert c[..] == [3, 4];
}

method TestArraySplit2() {
  var a := new int[3] [5, 10, 15];
  var b, c := ArraySplit(a);
  assert b[..] == [5];
  assert c[..] == [10, 15];
}
