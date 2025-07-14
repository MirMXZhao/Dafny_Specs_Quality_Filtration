function fact (n:nat): nat
{}

function factAcc (n:nat, a:int): int
{}

function factAlt(n:nat):int
{factAcc(n,1)}

lemma factAcc_correct (n:nat, a:int)
 ensures factAcc(n, a) == a*fact(n)
{
}

lemma factAlt_correct (n:nat)
 ensures factAlt(n) == fact(n)
{}

datatype List<T> = Nil | Cons(T, List<T>)

function length<T> (l: List<T>) : nat
{}

lemma {:induction false} length_non_neg<T> (l:List<T>)
    ensures length(l) >= 0
{}

function lengthTL<T> (l: List<T>, acc: nat) : nat
{}
lemma {:induction false}lengthTL_aux<T> (l: List<T>, acc: nat)
    ensures lengthTL(l, acc) == acc + length(l)
{}
lemma lengthEq<T> (l: List<T>)
    ensures length(l) == lengthTL(l,0)
{}

