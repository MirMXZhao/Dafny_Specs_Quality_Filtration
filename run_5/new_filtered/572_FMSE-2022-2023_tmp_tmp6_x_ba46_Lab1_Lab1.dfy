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