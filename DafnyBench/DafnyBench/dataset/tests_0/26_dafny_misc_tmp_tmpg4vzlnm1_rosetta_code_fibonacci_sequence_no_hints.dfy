function Fibonacci(n: nat): nat {}

method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{}

////////TESTS////////

method TestFibonacci1() {
  var result := Fibonacci(0);
  assert result == 0;
}

method TestFibonacci2() {
  var result := Fibonacci(5);
  assert result == 5;
}

method TestFibonacci3() {
  var result := Fibonacci(1);
  assert result == 1;
}

method TestFibonacciIterative1() {
  var f := FibonacciIterative(0);
  assert f == 0;
}

method TestFibonacciIterative2() {
  var f := FibonacciIterative(6);
  assert f == 8;
}

method TestFibonacciIterative3() {
  var f := FibonacciIterative(1);
  assert f == 1;
}
