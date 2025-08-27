newtype Odd = n : int | IsOddNat(n) witness 1

newtype Even = n : int | IsEvenNat(n) witness 2

newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

predicate IsOddNat(x: int) {
    (x >= 0) && (x % 2 == 1)
}

predicate IsEvenNat(x: int) {
    (x >= 0) && (x % 2 == 0)
}

lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{}

predicate IsPrime(x: int)
    requires x >= 0;
{
    x == 2 || forall d :: 2 <= d < x ==> x % d != 0
}

lemma AnyPrimeGreaterThanTwoIsOdd(x : int)
    requires x > 2;
    requires IsPrime(x);
    ensures IsOddNat(x);
{}

function add(x: int32, y: int32): int32 {}

function sub(x: int32, y: int32): int32 {}

function mul(x: int32, y: int32): int32 {}

function div(x: int32, y: int32): int32 
    requires y != 0; 
{}

function mod(x: int32, y: int32): int32
    requires y != 0; 
{}

function abs(x: int32): (r: int32)
    ensures r >= 0;
{}

////////TESTS////////

method Testadd1() {
  var result := add(5, 3);
  assert result == 8;
}

method Testadd2() {
  var result := add(-10, 7);
  assert result == -3;
}

method Testsub1() {
  var result := sub(10, 4);
  assert result == 6;
}

method Testsub2() {
  var result := sub(3, 8);
  assert result == -5;
}

method Testmul1() {
  var result := mul(6, 7);
  assert result == 42;
}

method Testmul2() {
  var result := mul(-4, 3);
  assert result == -12;
}

method Testdiv1() {
  var result := div(15, 3);
  assert result == 5;
}

method Testdiv2() {
  var result := div(17, 4);
  assert result == 4;
}

method Testmod1() {
  var result := mod(17, 5);
  assert result == 2;
}

method Testmod2() {
  var result := mod(20, 6);
  assert result == 2;
}

method Testabs1() {
  var result := abs(-15);
  assert result == 15;
}

method Testabs2() {
  var result := abs(8);
  assert result == 8;
}
