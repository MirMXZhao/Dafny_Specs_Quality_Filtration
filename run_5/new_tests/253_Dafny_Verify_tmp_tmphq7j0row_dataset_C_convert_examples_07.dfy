method main(n: int) returns (a: int, b: int)
    requires n >= 0
    ensures a + b == 3 * n
{}

////////TESTS////////

method TestMain1() {
  var a, b := main(5);
  assert a + b == 15;
}

method TestMain2() {
  var a, b := main(0);
  assert a + b == 0;
}
