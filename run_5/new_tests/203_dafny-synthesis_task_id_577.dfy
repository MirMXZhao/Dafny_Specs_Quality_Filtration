function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {}

method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
    {}

////////TESTS////////

method TestFactorialOfLastDigit1() {
  var fact := FactorialOfLastDigit(15);
  assert fact == Factorial(5);
}

method TestFactorialOfLastDigit2() {
  var fact := FactorialOfLastDigit(23);
  assert fact == Factorial(3);
}
