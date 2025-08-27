method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{}

////////TESTS////////

method TestProblem21() {
  var r, s := problem2(7, 5, 2, 3);
  assert r == 2;
  assert s == 3;
}

method TestProblem22() {
  var r, s := problem2(10, 4, 1, 8);
  assert r == 1;
  assert s == 8;
}
