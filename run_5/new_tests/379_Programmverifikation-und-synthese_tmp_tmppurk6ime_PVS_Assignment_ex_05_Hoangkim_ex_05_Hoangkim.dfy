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
  var result := fibIter(1);
  assert result == 1;
}

method TestFib2() {
  var result := fibIter(5);
  assert result == 5;
}

method TestFactIter1() {
  var result := factIter(0);
  assert result == 1;
}

method TestFactIter2() {
  var result := factIter(4);
  assert result == 24;
}

method TestGcdI1() {
  var result := gcdI(12, 8);
  assert result == 4;
}

method TestGcdI2() {
  var result := gcdI(15, 25);
  assert result == 5;
}
