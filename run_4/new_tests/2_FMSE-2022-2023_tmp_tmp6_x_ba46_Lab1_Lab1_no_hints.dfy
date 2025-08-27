newtype Odd = n : int | IsOddNat(n) witness 1

newtype Even = n : int | IsEvenNat(n) witness 2

newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

predicate IsOddNat(x: int) {}

predicate IsEvenNat(x: int) {}

lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{}

predicate IsPrime(x: int)
    requires x >= 0;
{}

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

method TestBelowZero1() {
  var operations := [1, 2, -4, 5];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == -1;
  assert s[4] == 4;
  assert result == true;
}

method TestBelowZero2() {
  var operations := [1, 2, 3, 1];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == 6;
  assert s[4] == 7;
  assert result == false;
}
