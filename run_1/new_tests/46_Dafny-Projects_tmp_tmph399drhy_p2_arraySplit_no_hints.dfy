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
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var b, c := ArraySplit(a);
  assert b[..] == [1, 2];
  assert c[..] == [3, 4];
}

method TestArraySplit2() {
  var a := new int[6];
  a[0] := 10; a[1] := 20; a[2] := 30; a[3] := 40; a[4] := 50; a[5] := 60;
  var b, c := ArraySplit(a);
  assert b[..] == [10, 20, 30];
  assert c[..] == [40, 50, 60];
}
