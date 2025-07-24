// RUN: %testDafnyForEachResolver "%s"


ghost predicate IsPrime(n: int)
{}

// The following theorem shows that there is an infinite number of primes
lemma AlwaysMorePrimes(k: int)
  ensures exists p :: k <= p && IsPrime(p)
{}

// Here is an alternative formulation of the theorem
lemma NoFiniteSetContainsAllPrimes(s: set<int>)
  ensures exists p :: IsPrime(p) && p !in s
{}

// ------------------------- lemmas and auxiliary definitions

ghost predicate AllPrimes(s: set<int>, bound: int)
{}

lemma GetLargerPrime(s: set<int>, bound: int) returns (p: int)
  requires AllPrimes(s, bound)
  ensures bound < p && IsPrime(p)
{}

ghost function product(s: set<int>): int
{}

lemma product_property(s: set<int>)
  requires forall x :: x in s ==> 1 <= x
  ensures 1 <= product(s) && forall x :: x in s ==> x <= product(s)
{}

lemma ProductPlusOneIsPrime(s: set<int>, q: int)
  requires AllPrimes(s, q) && q == product(s)
  ensures IsPrime(q+1)
{}

// The following lemma is essentially just associativity and commutativity of multiplication.
// To get this proof through, it is necessary to know that if x!=y and y==Pick...(s), then
// also y==Pick...(s - {x}).  It is for this reason that we use PickLargest, instead of
// picking an arbitrary element from s.
lemma RemoveFactor(x: int, s: set<int>)
  requires x in s
  ensures product(s) == x * product(s - {x})
{}

// This definition is like IsPrime above, except that the quantification is only over primes.
ghost predicate IsPrime_Alt(n: int)
{}

// To show that n is prime, it suffices to prove that it satisfies the alternate definition
lemma AltPrimeDefinition(n: int)
  requires IsPrime_Alt(n)
  ensures IsPrime(n)
{}

lemma Composite(c: int) returns (a: int, b: int)
  requires 2 <= c && !IsPrime(c)
  ensures 2 <= a < c && 2 <= b && a * b == c
  ensures IsPrime(a)
{}

ghost function PickLargest(s: set<int>): int
  requires s != {}
{}

lemma LargestElementExists(s: set<int>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
{}

lemma MulPos(a: int, b: int)
  requires 1 <= a && 1 <= b
  ensures a <= a * b
{}

// This axiom about % is needed.  Unfortunately, Z3 seems incapable of proving it.
lemma MulDivMod(a: nat, b: nat, c: nat, j: nat)
  requires a * b == c && j < a
  ensures (c+j) % a == j

