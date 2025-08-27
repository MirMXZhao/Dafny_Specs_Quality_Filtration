// recursive definition of factorial
function Factorial(n: nat): nat {}

// iterative implementation of factorial
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{}

