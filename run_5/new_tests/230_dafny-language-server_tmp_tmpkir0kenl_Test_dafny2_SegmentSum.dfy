function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{}

////////TESTS////////

method TestMaxSegSum1() {
  var a := [1, -3, 2, 1, -1];
  var k, m := MaxSegSum(a);
  assert k == 2;
  assert m == 4;
}

method TestMaxSegSum2() {
  var a := [-1, -2, -3];
  var k, m := MaxSegSum(a);
  assert k == 0;
  assert m == 0;
}
