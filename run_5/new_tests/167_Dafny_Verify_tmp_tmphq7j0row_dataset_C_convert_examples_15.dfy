method main(n: int, k: int) returns (k_out: int)
    requires n > 0;
	requires k > n;
	ensures k_out >= 0;
{}

////////TESTS////////

method TestMain1() {
  var k_out := main(5, 10);
  assert k_out >= 0;
}

method TestMain2() {
  var k_out := main(3, 7);
  assert k_out >= 0;
}
