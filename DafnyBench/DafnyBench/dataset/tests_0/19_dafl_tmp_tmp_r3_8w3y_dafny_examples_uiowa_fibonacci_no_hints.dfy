function fib(n: nat): nat
{}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{}

////////TESTS////////

method TestFib1() {
  assert fib(0) == 0;
}

method TestFib2() {
  assert fib(1) == 1;
}

method TestFib3() {
  assert fib(5) == 5;
}

method TestComputeFib1() {
  var f := ComputeFib(0);
  assert f == 0;
}

method TestComputeFib2() {
  var f := ComputeFib(1);
  assert f == 1;
}

method TestComputeFib3() {
  var f := ComputeFib(5);
  assert f == 5;
}
