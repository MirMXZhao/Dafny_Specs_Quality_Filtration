function fib(n: nat): nat
{}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{}