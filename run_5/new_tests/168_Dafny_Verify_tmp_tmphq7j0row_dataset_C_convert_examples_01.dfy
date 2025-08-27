method main() returns (t1: int, t2: int, x: int, y: int)
ensures y >= 1
{}

////////TESTS////////

method TestMain1() {
  var t1, t2, x, y := main();
  assert t1 == t1;
  assert t2 == t2;
  assert x == x;
  assert y >= 1;
}

method TestMain2() {
  var t1, t2, x, y := main();
  assert t1 == t1;
  assert t2 == t2;
  assert x == x;
  assert y >= 1;
}
