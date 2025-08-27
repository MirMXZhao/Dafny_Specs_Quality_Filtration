datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
decreases m
{}

predicate Odd(m: Nat)
decreases m
{
    match m
        case Zero => false
        case Succ(m') => Even(m')
}


predicate Even(m: Nat)
decreases m
{
    match m
        case Zero => true
        case Succ(m') => Odd(m')
}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{}