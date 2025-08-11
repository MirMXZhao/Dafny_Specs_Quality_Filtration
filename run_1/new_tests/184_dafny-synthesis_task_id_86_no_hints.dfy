method CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{}

////////TESTS////////

method TestCenteredHexagonalNumber1() {
  var result := CenteredHexagonalNumber(0);
  assert result == 1;
}

method TestCenteredHexagonalNumber2() {
  var result := CenteredHexagonalNumber(3);
  assert result == 19;
}
