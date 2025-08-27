method Triple (x: int) returns (r: int)
  ensures r == 3*x {}

method Caller() {}

method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y {}

method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y {}

method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y

method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{}

function Average (a: int, b: int): int {
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  ensures Average(2*r, 6*x) == 6*x
{}

////////TESTS////////

method TestTriple1() {
  var r := Triple(5);
  assert r == 15;
}

method TestTriple2() {
  var r := Triple(-3);
  assert r == -9;
}

method TestCaller1() {
  Caller();
}

method TestCaller2() {
  Caller();
}

method TestMinUnderSpec1() {
  var r := MinUnderSpec(10, 7);
  assert r <= 10 && r <= 7;
}

method TestMinUnderSpec2() {
  var r := MinUnderSpec(-5, 3);
  assert r <= -5 && r <= 3;
}

method TestMin1() {
  var r := Min(8, 12);
  assert r == 8;
}

method TestMin2() {
  var r := Min(15, 9);
  assert r == 9;
}

method TestMaxSum1() {
  var s, m := MaxSum(4, 7);
  assert s == 11;
  assert m == 7;
}

method TestMaxSum2() {
  var s, m := MaxSum(-2, 5);
  assert s == 3;
  assert m == 5;
}

method TestReconstructFromMaxSum1() {
  var x, y := ReconstructFromMaxSum(10, 6);
  assert x + y == 10;
  assert (x == 6 || y == 6) && x <= 6 && y <= 6;
}

method TestReconstructFromMaxSum2() {
  var x, y := ReconstructFromMaxSum(8, 5);
  assert x + y == 8;
  assert (x == 5 || y == 5) && x <= 5 && y <= 5;
}

method TestTriple'1() {
  var r := Triple'(4);
  assert Average(2*r, 24) == 24;
}

method TestTriple'2() {
  var r := Triple'(-2);
  assert Average(2*r, -12) == -12;
}
