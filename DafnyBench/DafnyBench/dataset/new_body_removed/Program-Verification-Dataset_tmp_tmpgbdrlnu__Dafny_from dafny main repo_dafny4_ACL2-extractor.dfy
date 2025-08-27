// RUN: %dafny /compile:0 /deprecation:0 /proverOpt:O:smt.qi.eager_threshold=30 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This is the Extractor Problem from section 11.8 of the ACL2 book,
// "Computer-Aided Reasoning: An Approach" by Kaufmann, Manolios, and
// Moore (2011 edition).

datatype List<T> = Nil | Cons(head: T, tail: List)

ghost function length(xs: List): nat
{}

// If "0 <= n < length(xs)", then return the element of "xs" that is preceded by
// "n" elements; otherwise, return an arbitrary value.
ghost opaque function nth<T(00)>(n: int, xs: List<T>): T
{}

ghost function nthWorker<T>(n: int, xs: List<T>): T
  requires 0 <= n < length(xs);
{}

ghost function append(xs: List, ys: List): List
{}

ghost function rev(xs: List): List
{}

ghost function nats(n: nat): List<int>
{}

ghost function xtr<T(00)>(mp: List<int>, lst: List): List
{}

lemma ExtractorTheorem<T(00)>(xs: List)
  ensures xtr(nats(length(xs)), xs) == rev(xs);
{}

// auxiliary lemmas and proofs follow

// lemmas about length

lemma XtrLength(mp: List<int>, lst: List)
  ensures length(xtr(mp, lst)) == length(mp);
{
}

lemma NatsLength(n: nat)
  ensures length(nats(n)) == n;
{
}

lemma AppendLength(xs: List, ys: List)
  ensures length(append(xs, ys)) == length(xs) + length(ys);
{
}

lemma RevLength(xs: List)
  ensures length(rev(xs)) == length(xs);
{}

// you can prove two lists equal by proving their elements equal

lemma EqualElementsMakeEqualLists<T(00)>(xs: List, ys: List)
  requires length(xs) == length(ys)
  requires forall i :: 0 <= i < length(xs) ==> nth(i, xs) == nth(i, ys)
  ensures xs == ys
{}

// here is the theorem, but applied to the ith element

lemma {} ExtractorLemma<T(00)>(i: int, xs: List)
  requires 0 <= i < length(xs);
  ensures nth(i, xtr(nats(length(xs)), xs)) == nth(i, rev(xs));
{}

// lemmas about what nth gives on certain lists

lemma NthXtr<T(00)>(i: int, mp: List<int>, lst: List<T>)
  requires 0 <= i < length(mp);
  ensures nth(i, xtr(mp, lst)) == nth(nth(i, mp), lst);
{}

lemma NthNats(i: int, n: nat)
  requires 0 <= i < n;
  ensures nth(i, nats(n)) == n - 1 - i;
{}

lemma NthNatsWorker(i: int, n: nat)
  requires 0 <= i < n && length(nats(n)) == n;
  ensures nthWorker(i, nats(n)) == n - 1 - i;
{
}

lemma NthRev<T(00)>(i: int, xs: List)
  requires 0 <= i < length(xs) == length(rev(xs));
  ensures nthWorker(i, rev(xs)) == nthWorker(length(xs) - 1 - i, xs);
{}

lemma NthAppendA<T(00)>(i: int, xs: List, ys: List)
  requires 0 <= i < length(xs);
  ensures nth(i, append(xs, ys)) == nth(i, xs);
{}

lemma NthAppendB<T(00)>(i: int, xs: List, ys: List)
  requires length(xs) <= i < length(xs) + length(ys);
  ensures nth(i, append(xs, ys)) == nth(i - length(xs), ys);
{}

