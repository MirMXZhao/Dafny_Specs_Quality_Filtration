
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
















method TestFibIter1() {
  var a := fibIter(1);
  assert a == fib(1);
}

method TestFibIter2() {
  var a := fibIter(5);
  assert a == fib(5);
}

method TestFactIter1() {
  var a := factIter(0);
  assert a == fact(0);
}

method TestFactIter2() {
  var a := factIter(4);
  assert a == fact(4);
}

method TestGcdI1() {
  var g := gcdI(12, 8);
  assert g == gcd(12, 8);
}

method TestGcdI2() {
  var g := gcdI(7, 3);
  assert g == gcd(7, 3);
}
