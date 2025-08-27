// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {}

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{}

