predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
{}

////////TESTS////////

method TestCountSubstringsWithSumOfDigitsEqualToLength1() {
  var s := "1210";
  var count := CountSubstringsWithSumOfDigitsEqualToLength(s);
  assert count == 6;
}

method TestCountSubstringsWithSumOfDigitsEqualToLength2() {
  var s := "123";
  var count := CountSubstringsWithSumOfDigitsEqualToLength(s);
  assert count == 4;
}
