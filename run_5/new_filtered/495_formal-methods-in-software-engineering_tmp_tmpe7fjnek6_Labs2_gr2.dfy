datatype Nat = Zero | Succ(Pred: Nat)

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

function add(m: Nat, n: Nat) : Nat
decreases m
{}

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
{
    (m.Zero? && n.Succ?) ||
    (m.Succ? && n.Succ? && lt(m.Pred, n.Pred))
}

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

function rev<T> (l: List<T>) : List<T>
{}

lemma AppNil<T>(l: List<T>)
ensures app(l, Nil) == l
{
    //
}

lemma LR1<T> (l: List<T>, x: T)
ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
{
    //
}

lemma RevRev<T>(l: List<T>)
ensures rev(rev(l)) == l
{}