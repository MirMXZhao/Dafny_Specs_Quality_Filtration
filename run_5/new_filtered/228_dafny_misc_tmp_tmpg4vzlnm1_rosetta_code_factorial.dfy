function Factorial(n: nat): nat {}

method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{}