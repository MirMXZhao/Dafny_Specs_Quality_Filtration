function fib(n: nat): nat
  decreases n;
{}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{}

////////TESTS////////

method TestComputeFib1() {
  var f := ComputeFib(0);
  assert f == 1;
}

method TestComputeFib2() {
  var f := ComputeFib(5);
  assert f == 8;
}
