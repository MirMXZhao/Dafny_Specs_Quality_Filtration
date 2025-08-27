function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {}

    method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
    {}