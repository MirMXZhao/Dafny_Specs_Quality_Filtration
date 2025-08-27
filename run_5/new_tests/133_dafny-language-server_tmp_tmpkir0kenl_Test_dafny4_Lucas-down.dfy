// RUN: %dafny /compile:0 /arith:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate Bit(k: nat, n: nat)
{
  if k == 0 then n % 2 == 1
  else Bit(k-1, n / 2)
}

function BitSet(n: nat): set<nat>
{}

lemma BitSize(i: nat, n: nat)
  requires Bit(i, n)
  ensures i < n
{
}

predicate EVEN(n: nat)
{
  n % 2 == 0
}

function binom(a: nat, b: nat): nat
{}

lemma Lucas_Binary''(a: nat, b: nat)
  ensures binom(a, b) % 2 == if EVEN(a) && !EVEN(b) then 0 else binom(a / 2, b / 2) % 2
{}

function Suc(S: set<nat>): set<nat>
{}

lemma SucElements(S: set<nat>)
  ensures forall x :: x in S <==> (x+1) in Suc(S)
{
}

lemma BitSet_Property(n: nat)
  ensures BitSet(n) - {0} == Suc(BitSet(n / 2))
{}

lemma Lucas_Theorem'(m: nat, n: nat)
  ensures BitSet(m) <= BitSet(n) <==> !EVEN(binom(n, m))
{}

////////TESTS////////

method TestBitSet1() {
  var result := BitSet(5);
  assert result == {0, 2};
}

method TestBitSet2() {
  var result := BitSet(7);
  assert result == {0, 1, 2};
}

method TestBinom1() {
  var result := binom(3, 2);
  assert result == 3;
}

method TestBinom2() {
  var result := binom(4, 2);
  assert result == 6;
}

method TestSuc1() {
  var result := Suc({1, 3, 5});
  assert result == {2, 4, 6};
}

method TestSuc2() {
  var result := Suc({0, 2});
  assert result == {1, 3};
}
