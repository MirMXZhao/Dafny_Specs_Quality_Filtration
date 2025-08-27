method main(n: int) returns (sum: int, i: int)
requires n >= 0
{}

////////TESTS////////

method TestMain1() {
  var sum, i := main(5);
  assert sum == 15;
  assert i == 5;
}

method TestMain2() {
  var sum, i := main(0);
  assert sum == 0;
  assert i == 0;
}
