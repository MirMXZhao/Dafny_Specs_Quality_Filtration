function Fibonacci(n: nat): nat {}

method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{}

////////TESTS////////

method TestFibonacci1() {
  var f := FibonacciIterative(0);
  assert f == 0;
}

method TestFibonacci2() {
  var f := FibonacciIterative(5);
  assert f == 5;
}

method TestFibonacciIterative1() {
  var f := FibonacciIterative(1);
  assert f == 1;
}

method TestFibonacciIterative2() {
  var f := FibonacciIterative(6);
  assert f == 8;
}
