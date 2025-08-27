method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
{}

////////TESTS////////

method TestMain1() {
  var x, m := main(5);
  assert 0 <= m && m < 5;
}

method TestMain2() {
  var x, m := main(10);
  assert 0 <= m && m < 10;
}
