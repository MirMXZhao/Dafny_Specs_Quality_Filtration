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

////////TESTS////////

method TestAdd1() {
  var result := Add(S(Zero), S(S(Zero)));
  assert result == S(S(S(Zero)));
}

method TestAdd2() {
  var result := Add(Zero, S(Zero));
  assert result == S(Zero);
}

method TestLessThan1() {
  var result := LessThan(Zero, S(Zero));
  assert result == true;
}

method TestLessThan2() {
  var result := LessThan(S(Zero), Zero);
  assert result == false;
}

method TestSize1() {
  var result := Size(Append(S(Zero), Append(S(S(Zero)), Nil)));
  assert result == S(S(Zero));
}

method TestSize2() {
  var result := Size(Nil);
  assert result == Zero;
}

method TestConcatenation1() {
  var result := Concatenation(Append(S(Zero), Nil), Append(S(S(Zero)), Nil));
  assert result == Append(S(Zero), Append(S(S(Zero)), Nil));
}

method TestConcatenation2() {
  var result := Concatenation(Nil, Append(S(Zero), Nil));
  assert result == Append(S(Zero), Nil);
}

method TestReverseList1() {
  var result := ReverseList(Append(S(Zero), Append(S(S(Zero)), Nil)));
  assert result == Append(S(S(Zero)), Append(S(Zero), Nil));
}

method TestReverseList2() {
  var result := ReverseList(Nil);
  assert result == Nil;
}
