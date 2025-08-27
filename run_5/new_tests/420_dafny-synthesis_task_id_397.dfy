method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{}

////////TESTS////////

method TestMedianOfThree1() {
  var median := MedianOfThree(3, 1, 2);
  assert median == 2;
}

method TestMedianOfThree2() {
  var median := MedianOfThree(5, 5, 1);
  assert median == 5;
}
