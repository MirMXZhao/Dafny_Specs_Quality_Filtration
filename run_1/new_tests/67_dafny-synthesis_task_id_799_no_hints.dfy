method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{}

////////TESTS////////

method TestRotateLeftBits1() {
  var result := RotateLeftBits(0b00000000000000000000000000001111, 4);
  assert result == 0b00000000000000000000000011110000;
}

method TestRotateLeftBits2() {
  var result := RotateLeftBits(0b10000000000000000000000000000001, 1);
  assert result == 0b00000000000000000000000000000011;
}
