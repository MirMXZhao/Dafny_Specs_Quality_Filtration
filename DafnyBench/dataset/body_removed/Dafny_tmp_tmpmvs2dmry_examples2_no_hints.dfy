method add_by_inc(x: nat, y:nat) returns (z:nat)
ensures z == x+y;
{}

method Product(m: nat, n:nat) returns (res:nat)
ensures res == m*n;
{}

method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0;
ensures res == gcd(m,n);
{}

function gcd(m: nat, n: nat) : nat
requires m>0 && n>0;
{}

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0;
ensures r == exp(x0, n0);
{}

function exp(x: real, n: nat) :real
{}

// method add_by_inc_vc(x: int, y:int) returns (z:int)
// {}


