method Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
{}

////////TESTS////////

method TestMin1() {
  var minValue := Min(5, 3);
  assert minValue == 3;
}

method TestMin2() {
  var minValue := Min(-2, 7);
  assert minValue == -2;
}
