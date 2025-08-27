method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
{}

////////TESTS////////

method TestNonZeroReturn1() {
  var y := nonZeroReturn(5);
  assert y != 0;
}

method TestNonZeroReturn2() {
  var y := nonZeroReturn(-3);
  assert y != 0;
}
