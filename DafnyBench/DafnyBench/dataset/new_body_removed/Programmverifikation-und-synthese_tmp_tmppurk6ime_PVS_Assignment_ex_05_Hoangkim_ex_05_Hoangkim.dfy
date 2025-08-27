
//Problem01
function fib(n: nat):nat
{}

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{}
//# 2 pts

//Problem02
function fact(n:nat):nat
{}

method factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
{} 
//# 3 pts
//Problem03
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{}

method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
    {}
//# 3 pts


// # sum: 9 pts














