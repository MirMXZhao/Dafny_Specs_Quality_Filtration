function fact(n: nat): nat 
    ensures fact(n) >= 1
{}

method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{}
