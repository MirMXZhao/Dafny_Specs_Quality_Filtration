datatype Nat = Zero | Succ(Pred: Nat)

/*

Nat: Zero, Succ(Zero), Succ(Succ(Zero)), ...

*/

lemma Disc(n: Nat)
ensures n.Succ? || n.Zero?
{
    //
}

lemma LPred(n: Nat)
ensures Succ(n).Pred == n
{
    //
}

// Succ(m') > m'

function add(m: Nat, n: Nat) : Nat
{}

// add(m, Zero) = m

lemma AddZero(m: Nat)
ensures add(m, Zero) == m
{
    //
}

lemma AddAssoc(m: Nat, n: Nat, p: Nat)
ensures add(m, add(n, p)) == add(add(m, n), p)
{
    //
}

lemma AddComm(m: Nat, n: Nat)
ensures add(m, n) == add(n, m)
{}

predicate lt(m: Nat, n: Nat)
{}

lemma Test1(n:Nat)
ensures lt(n, Succ(Succ(n)))
{
    //
}

lemma Test2(n: Nat)
ensures n < Succ(n)
{
    //
}

/*
lemma L1()
ensures exists x: Nat :: x == Zero.Pred 
{

    //
}
*/
/*
lemma L2(m: Nat, n: Nat)
ensures lt(m, n) == lt(n, m)
{
    //
}
*/
lemma LtTrans(m: Nat, n: Nat, p: Nat)
requires lt(m, n)
requires lt(n, p)
ensures lt(m, p)
{}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

lemma Disc2<T>(l: List<T>, a: T)
ensures Cons(a, l).head == a && Cons(a, l).tail == l
{
    //
}

function size<T>(l: List<T>): nat
{}

function app<T>(l1: List<T>, l2: List<T>) : List<T>
{}

lemma LenApp<T>(l1: List<T>, l2: List<T>)
ensures size(app(l1, l2)) == size(l1) + size(l2)
{
    //
}

/*
 (1,(2,3)) -> ((3,2),1)
 (x, l') -> (rev(l'), x)
*/

function rev<T> (l: List<T>) : List<T>
{}

lemma AppNil<T>(l: List<T>)
ensures app(l, Nil) == l
{
    //
}

/*
lemma RevApp<T>(l1: List<T>, l2: List<T>)
ensures rev(app(l1, l2)) == app(rev(l2), rev(l1))
{}
*/
lemma LR1<T> (l: List<T>, x: T)
ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
{
    //
}

lemma RevRev<T>(l: List<T>)
ensures rev(rev(l)) == l
{}


/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

