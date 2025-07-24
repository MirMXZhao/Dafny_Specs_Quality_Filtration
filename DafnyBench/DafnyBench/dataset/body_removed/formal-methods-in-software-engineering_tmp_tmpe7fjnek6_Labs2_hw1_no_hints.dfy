/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
{}

predicate Odd(m: Nat)
{}


predicate Even(m: Nat)
{}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{}
