method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
{}

////////TESTS////////

method TestSumAndAverage1() {
  var sum, average := SumAndAverage(5);
  assert sum == 15;
  assert average == 3.0;
}

method TestSumAndAverage2() {
  var sum, average := SumAndAverage(3);
  assert sum == 6;
  assert average == 2.0;
}
