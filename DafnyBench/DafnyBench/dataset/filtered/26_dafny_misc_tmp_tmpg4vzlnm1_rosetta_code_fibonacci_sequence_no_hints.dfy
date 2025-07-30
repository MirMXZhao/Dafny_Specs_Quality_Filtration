function Fibonacci(n: nat): nat {}

method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{}