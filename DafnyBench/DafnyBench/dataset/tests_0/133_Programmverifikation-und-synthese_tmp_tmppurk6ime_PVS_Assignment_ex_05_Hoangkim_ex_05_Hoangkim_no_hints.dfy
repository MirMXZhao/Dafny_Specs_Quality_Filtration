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

method testfib1() {
  assert fib(5) == 5;
}

method testfib2() {
  assert fib(7) == 13;
}

method testfib3() {
  assert fib(0) == 0;
}

method testfibIter1() {
  var a := fibIter(5);
  assert a == 5;
}

method testfibIter2() {
  var a := fibIter(7);
  assert a == 13;
}

method testfibIter3() {
  var a := fibIter(1);
  assert a == 1;
}

method testfact1() {
  assert fact(5) == 120;
}

method testfact2() {
  assert fact(0) == 1;
}

method testfact3() {
  assert fact(3) == 6;
}

method testfactIter1() {
  var a := factIter(5);
  assert a == 120;
}

method testfactIter2() {
  var a := factIter(0);
  assert a == 1;
}

method testfactIter3() {
  var a := factIter(3);
  assert a == 6;
}

method testgcd1() {
  assert gcd(12, 8) == 4;
}

method testgcd2() {
  assert gcd(15, 25) == 5;
}

method testgcd3() {
  assert gcd(7, 7) == 7;
}

method testgcdI1() {
  var g := gcdI(12, 8);
  assert g == 4;
}

method testgcdI2() {
  var g := gcdI(15, 25);
  assert g == 5;
}

method testgcdI3() {
  var g := gcdI(7, 7);
  assert g == 7;
}
