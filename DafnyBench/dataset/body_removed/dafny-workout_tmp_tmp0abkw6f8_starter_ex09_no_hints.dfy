function fib(n: nat): nat
{}

method ComputeFib(n: nat) returns (b: nat)
	ensures b == fib(n)
{}

method Main()
{}

