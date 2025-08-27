method main(n : int) returns (i: int, x: int, y:int)
requires n >= 0
ensures (i % 2 != 0) || (x == 2 * y)
{}

////////TESTS////////

method TestMain1() {
  var i, x, y := main(5);
  assert i == 1;
  assert x == 4;
  assert y == 2;
}

method TestMain2() {
  var i, x, y := main(0);
  assert i == 2;
  assert x == 6;
  assert y == 3;
}
