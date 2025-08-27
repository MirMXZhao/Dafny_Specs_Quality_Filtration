method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{}

////////TESTS////////

method TestSqrt1() {
  var r := sqrt(4.0);
  assert r == 2.0;
}

method TestSqrt2() {
  var r := sqrt(9.0);
  assert r == 3.0;
}
