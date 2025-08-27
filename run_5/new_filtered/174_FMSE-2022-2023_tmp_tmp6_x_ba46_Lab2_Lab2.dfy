datatype Nat = Zero | S(Pred: Nat)

lemma SIsInjective(x: Nat, y: Nat)
    ensures S(x) == S(y) ==> x == y
{}

lemma ZeroIsDifferentFromSuccessor(n: Nat)
    ensures S(n) != Zero
{}

function Add(x: Nat, y: Nat) : Nat
    decreases y
{}

 lemma {:induction n} ZeroAddNeutral(n: Nat)
    ensures Add(n, Zero) == Add(Zero, n) == n
{}

lemma {:induction n} ZeroAddCommutative(n: Nat)
    ensures Add(Zero, n) == Add(n, Zero)
{}

lemma {:induction x, y} AddCommutative(x: Nat, y: Nat)
    ensures Add(x, y) == Add(y, x)
    decreases x, y
{}

lemma {:induction x, y} ZeroAddAssociative(x: Nat, y: Nat)
    ensures Add(Add(Zero, x), y) == Add(Zero, Add(x, y))
{}

lemma {:induction x, y} AddAssociative(x: Nat, y: Nat, z: Nat)
    ensures Add(Add(x, y), z) == Add(x, Add(y, z))
    decreases z
{}

predicate LessThan(x: Nat, y: Nat)
    decreases x, y
{
    (x.Zero? && y.S?) || (x.S? && y.S? && LessThan(x.Pred, y.Pred))
}

lemma {:induction y, z} LessThanIsTransitiveWithZero(y: Nat, z: Nat)
    requires LessThan(Zero, y)
    requires LessThan(y, z)
    ensures LessThan(Zero, z)
{}

lemma {:induction x, y, z} LessThanIsTransitive(x: Nat, y: Nat, z: Nat)
    requires LessThan(x, y)
    requires LessThan(y, z)
    ensures LessThan(x, z)
    decreases x
{}

datatype List<T> = Nil | Append(head: T, tail: List)

function Size(l: List<Nat>): Nat
    decreases l
{}

function Concatenation(l1: List<Nat>, l2: List<Nat>) : List<Nat>
    decreases l1, l2
{}

lemma {:induction l1, l2} SizeOfConcatenationIsSumOfSizes(l1: List<Nat>, l2: List<Nat>)
    ensures Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2))
    decreases l1, l2
{}

function ReverseList(l: List<Nat>) : List<Nat>
    decreases l
{}

lemma {:induction l, n} ReversalOfConcatenationWithHead(l: List<Nat>, n: Nat)
    ensures ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l))
    decreases l, n
{}

lemma {:induction l} DoubleReversalResultsInInitialList(l: List<Nat>)
    ensures l == ReverseList(ReverseList(l))
{}