method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
{}

////////TESTS////////

method TestSwapBitvectors1() {
  var x, y := SwapBitvectors(0x0F, 0xA5);
  assert x == 0xA5;
  assert y == 0x0F;
}

method TestSwapBitvectors2() {
  var x, y := SwapBitvectors(0xFF, 0x00);
  assert x == 0x00;
  assert y == 0xFF;
}
