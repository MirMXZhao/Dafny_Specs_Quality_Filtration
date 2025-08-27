method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
{}

////////TESTS////////

method TestMinOfThree1() {
  var min := MinOfThree(5, 3, 8);
  assert min == 3;
}

method TestMinOfThree2() {
  var min := MinOfThree(10, 15, 7);
  assert min == 7;
}
