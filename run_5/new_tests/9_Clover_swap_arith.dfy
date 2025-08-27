method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X

{}

////////TESTS////////

method TestSwapArithmetic1() {
  var x, y := SwapArithmetic(5, 10);
  assert x == 10;
  assert y == 5;
}

method TestSwapArithmetic2() {
  var x, y := SwapArithmetic(-3, 7);
  assert x == 7;
  assert y == -3;
}
