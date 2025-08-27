function Factorial(n: nat): nat
{}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{}

////////TESTS////////

method TestComputeFactorial1() {
  var u := ComputeFactorial(1);
  assert u == 1;
}

method TestComputeFactorial2() {
  var u := ComputeFactorial(5);
  assert u == 120;
}
