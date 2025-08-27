method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{}

////////TESTS////////

method TestSumOfCommonDivisors1() {
  var sum := SumOfCommonDivisors(12, 18);
  assert sum == 22;
}

method TestSumOfCommonDivisors2() {
  var sum := SumOfCommonDivisors(7, 11);
  assert sum == 1;
}
