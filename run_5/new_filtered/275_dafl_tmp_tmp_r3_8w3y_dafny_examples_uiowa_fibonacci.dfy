function fib(n: nat): nat
  decreases n;
{}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{}