function fib(n: nat):nat
{}

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{}

function fact(n:nat):nat
{}

method factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
{} 

function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{}

method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
    {}

////////TESTS////////

method TestFib1() {
  assert fib(5) == 5;
}

method TestFib2() {
  assert fib(7) == 13;
}

method TestFibIter1() {
  var a := fibIter(5);
  assert a == 5;
}

method TestFibIter2() {
  var a := fibIter(7);
  assert a == 13;
}

method TestFact1() {
  assert fact(5) == 120;
}

method TestFact2() {
  assert fact(4) == 24;
}

method TestFactIter1() {
  var a := factIter(5);
  assert a == 120;
}

method TestFactIter2() {
  var a := factIter(4);
  assert a == 24;
}

method TestGcd1() {
  assert gcd(12, 8) == 4;
}

method TestGcd2() {
  assert gcd(15, 10) == 5;
}

method TestGcdI1() {
  var g := gcdI(12, 8);
  assert g == 4;
}

method TestGcdI2() {
  var g := gcdI(15, 10);
  assert g == 5;
}
