/*
 * Task 2: Define in Dafny the conatural numbers as a coinductive datatype
 * 
 * Being a coinductive data type, it's required that we have a base case constructor and an inductive one 
 * (as is the case with inductive ones as well)
 */
codatatype Conat = Zero | Succ(Pred: Conat)

// Exercise (a): explain why the following coinductive property does NOT hold
// lemma ConstructorConat(n: Conat)
    // ensures n != Succ(n)
// {}

// Exercise (b): show that the constructor successor is injective
greatest lemma ConstructorInjective(x: Conat, y: Conat)
    ensures Succ(x) == Succ(y) ==> x == y
{}

// Exercise (c): define the ∞ constant (as a corecursive function)
// We use a co-recursive call using the Succ constructor on the result, producing an infinite call stack
function inf(n: Conat): Conat
{
    Succ(inf(n))
}

// Exercise (d): define the addition of conaturals
// Similar to add function over the Nat datatype (See Lab2)
function add(x: Conat, y: Conat) : Conat
{}

// Exercise (e): show that by adding ∞ to itself it remains unchanged
// Because the focus is on greatest fixed-point we need to use a co-predicate
// Aptly renamed to greatest predicate
greatest predicate InfinityAddition()
{}

// Task 3: Define the parametric streams as a coinductive datatype where s ranges over streams
codatatype Stream<A> = Cons(head: A, tail: Stream<A>)

// Exercise (a): corecursively define the pointwise addition of two streams of integers
// After performing the addition of the value in the heads, proceed similarly with the tails
function addition(a: Stream<int>, b: Stream<int>): Stream<int>
{}

// Exercise (b): define a parametric integer constant stream
// An infinite stream with the same value
function cnst(a: int): Stream<int>
{}

// Exercise (c): prove by coinduction that add(s, cnst(0)) = s;
// The proof tried below is not complete, however, by telling Dafny that we are dealing with a colemma,
// Aptly renamed to greatest lemma, it is able to reason and prove the post-condition by itself
greatest lemma additionWithZero(a : Stream<int>)
    ensures addition(a, cnst(0)) == a
{}

// Exercise (d): define coinductively the predicate
greatest predicate leq(a: Stream<int>, b: Stream<int>)
{}

// Exercise (e): (e) define the stream blink
function blink(): Stream<int>
{}

// Exercise (f): prove by coinduction that leq(cnst(0), blink)
lemma CnstZeroLeqBlink()
    ensures leq(cnst(0), blink())
{ 
}

// Exercise (g): define a function that ”zips” two streams
// A stream formed by alternating the elements of both streams one by one
function zip(a: Stream<int>, b: Stream<int>): Stream<int>
{}

// Exercise (h): prove that zipping cnst(0) and cnst(1) yields blink
// By using a greatest lemma, Dafny can reason on its own
greatest lemma ZipCnstZeroCnstOneEqualsBlink()
    ensures zip(cnst(0), cnst(1)) == blink()
{}
