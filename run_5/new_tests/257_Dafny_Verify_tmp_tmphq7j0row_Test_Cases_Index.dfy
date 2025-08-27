method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    i := n/2;
}

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{}

method Max(x: int, y: int) returns (m: int) {}

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{}

////////TESTS////////

method TestIndex1() {
  var i := Index(10);
  assert 0 <= i < 10;
}

method TestIndex2() {
  var i := Index(1);
  assert 0 <= i < 1;
}

method TestMin1() {
  var m := Min(5, 3);
  assert m <= 5 && m <= 3;
  assert m == 5 || m == 3;
}

method TestMin2() {
  var m := Min(-2, 7);
  assert m <= -2 && m <= 7;
  assert m == -2 || m == 7;
}

method TestMax1() {
  var m := Max(8, 12);
}

method TestMax2() {
  var m := Max(-5, -1);
}

method TestMaxSum1() {
  var s, m := MaxSum(4, 7);
  assert s == 11;
  assert m == 7;
}

method TestMaxSum2() {
  var s, m := MaxSum(9, 3);
  assert s == 12;
  assert m == 9;
}

method TestReconstructFromMaxSum1() {
  var x, y := ReconstructFromMaxSum(10, 6);
  assert 10 == x + y;
  assert (6 == x || 6 == y) && x <= 6 && y <= 6;
}

method TestReconstructFromMaxSum2() {
  var x, y := ReconstructFromMaxSum(8, 5);
  assert 8 == x + y;
  assert (5 == x || 5 == y) && x <= 5 && y <= 5;
}
