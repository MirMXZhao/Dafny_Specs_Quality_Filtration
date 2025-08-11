method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{}

////////TESTS////////

method TestSumOfFourthPowerOfOddNumbers1() {
  var sum := SumOfFourthPowerOfOddNumbers(1);
  assert sum == 1;
}

method TestSumOfFourthPowerOfOddNumbers2() {
  var sum := SumOfFourthPowerOfOddNumbers(2);
  assert sum == 98;
}
