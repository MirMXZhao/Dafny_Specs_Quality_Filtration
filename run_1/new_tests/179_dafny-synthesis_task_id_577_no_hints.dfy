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
  var fact := FactorialOfLastDigit(1234);
  assert fact == Factorial(4);
}

method TestFactorialOfLastDigit2() {
  var fact := FactorialOfLastDigit(567);
  assert fact == Factorial(7);
}
