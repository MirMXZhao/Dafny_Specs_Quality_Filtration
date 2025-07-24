/// Types defined as part of Tasks 3, 5 and 9

// Since we have created the IsOddNat predicate we use it to define the new Odd subsort
newtype Odd = n : int | IsOddNat(n) witness 1

// Since we have created the IsEvenNat predicate we use it to define the new Even subsort
newtype Even = n : int | IsEvenNat(n) witness 2

/*
 * We use int as the native type, so that the basic operations are available. 
 * However, we restrict the domain in order to accomodate the requirements.
 */
newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

/// Task 2

/*
 * In order for an integer to be a natural, odd number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 1.
 */
predicate IsOddNat(x: int) {}

/// Task 4

/*
 * In order for an integer to be a natural, even number, two requirements must be satisfied:
 * The integer in cause must be positive and the remainder of the division by 2 must be 0.
 */
predicate IsEvenNat(x: int) {}

/// Task 6

/*
 * In order to prove the statement, we rewrite the two numbers to reflect their form:
 * The sum between a multiple of 2 and 1.
 *
 * By rewriting them like this and then adding them together, the sum is shown to
 * be a multiple of 2 and thus, an even number.
 */
lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{}

/// Task 7
/*
 * In order for an integer to be a natural, prime number, two requirements must be satisfied:
 * The integer in cause must be natural (positive) and must have exactly two divisors:
 * 1 and itself.
 *
 * Aside from two, which is the only even prime, we test the primality by checking if there
 * is no number greater or equal to 2 that the number in cause is divisible with.
 */
predicate IsPrime(x: int)
    requires x >= 0;
{}

/// Task 8
/*
 * It is a known fact that any prime divided by any number, aside from 1 and itself,
 * will yield a non-zero remainder.
 * 
 * Thus, when dividing a prime (other than 2) by 2, the only non-zero remainder possible 
 * is 1, therefore making the number an odd one.
 */
lemma AnyPrimeGreaterThanTwoIsOdd(x : int)
    requires x > 2;
    requires IsPrime(x);
    ensures IsOddNat(x);
{}

/* 
 * Task 9 
 * Defined the basic arithmetic functions.
 * Also defined the absolute value.
 * 
 * Over/Underflow are represented by the return of 0.
 */
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

