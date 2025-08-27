function fib(n: nat): nat
decreases n
{}

method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
{}

method fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
{}

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
{}

////////TESTS////////

method TestFibonacci11() {
  var f := fibonacci1(0);
  assert f == 0;
}

method TestFibonacci12() {
  var f := fibonacci1(5);
  assert f == 5;
}

method TestFibonacci21() {
  var f := fibonacci2(1);
  assert f == 1;
}

method TestFibonacci22() {
  var f := fibonacci2(6);
  assert f == 8;
}

method TestFibonacci31() {
  var f := fibonacci3(2);
  assert f == 1;
}

method TestFibonacci32() {
  var f := fibonacci3(7);
  assert f == 13;
}
