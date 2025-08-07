function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{}

////////TESTS////////

method TestSum1() {
  var a := [1, 2, 3, 4, 5];
  var result := Sum(a, 1, 3);
  assert result == 5;
}

method TestSum2() {
  var a := [1, -2, 3, -1, 2];
  var result := Sum(a, 0, 0);
  assert result == 0;
}

method TestSum3() {
  var a := [-1, -2, -3];
  var result := Sum(a, 0, 3);
  assert result == -6;
}

method TestMaxSegSum1() {
  var a := [1, -2, 3, -1, 2];
  var k, m := MaxSegSum(a);
  assert 0 <= k <= m <= |a|;
  assert forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m);
}

method TestMaxSegSum2() {
  var a := [-1, -2, -3];
  var k, m := MaxSegSum(a);
  assert 0 <= k <= m <= |a|;
  assert forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m);
}

method TestMaxSegSum3() {
  var a := [5];
  var k, m := MaxSegSum(a);
  assert 0 <= k <= m <= |a|;
  assert forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m);
}
