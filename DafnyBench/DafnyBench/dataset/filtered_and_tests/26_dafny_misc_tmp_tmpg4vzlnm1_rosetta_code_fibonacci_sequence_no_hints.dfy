// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {}

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{}



method TestFibonacciIterative1() {
  var f := FibonacciIterative(0);
  assert f == Fibonacci(0);
}

method TestFibonacciIterative2() {
  var f := FibonacciIterative(5);
  assert f == Fibonacci(5);
}
