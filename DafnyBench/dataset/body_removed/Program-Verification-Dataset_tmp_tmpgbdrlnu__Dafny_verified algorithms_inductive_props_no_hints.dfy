// This file demonstrates how to "close" a critical "gap" between definitions
// between Dafny and Coq.

// In general, most commonly-used "building blocks" in Coq can be mapped to Dafny:
// [Coq]                        [Dafny]
// --------------------------------------------------------------------
// Inductive (Set)              datatype
// Definition                   function/predicate
// Fixpoint                     function/predicate (with `decreases`)
// Theorem & Proof              lemma
// Type (Set, e.g. `list nat`)  still a type (e.g. `seq<nat>`)
// Type (Prop, e.g. `1+1==2`)   encode in `requires` or `ensures`
// N/A (at least NOT built-in)  method (imperative programming)
//
// Inductive (Prop)             ??? (discussed in this file)


// Dafny's way to define Coq's `Fixpoint` predicate:
ghost predicate even(n: nat) {}
// all below are automatically proved:
lemma a0() ensures even(4) {}
lemma a1() ensures !even(3) {}
lemma a2(n: nat) requires even(n) ensures even(n + 2) {}
lemma a3(n: nat) requires even(n + 2) ensures even(n) {}


// Dafny lacks syntax to define `Inductive` Prop like in Coq.
// We'll show two workarounds for this.

// Workaround 1: simulate with "rules"
datatype EvenRule =
  | ev_0
  | ev_SS(r: EvenRule)
{
  ghost function apply(): nat {}
}
ghost predicate Even(n: nat) {}
// then we can prove by "constructing" or "destructing" just like in Coq:
lemma b0() ensures Even(4) {
}
lemma b1() ensures !Even(3) {}
lemma b2(n: nat) requires Even(n) ensures Even(n + 2) {}
lemma b3(n: nat) requires Even(n + 2) ensures Even(n) {}


// Workaround 2: using "higher-order" predicates
type P = nat -> bool
ghost predicate Ev(ev: P) {}
// we explicitly say that `ev` is the "strictest" `P` that satisfies `Ev`:
ghost predicate Minimal(Ev: P -> bool, ev: P) {}
// In this approach, some lemmas are a bit tricky to prove...
lemma c0(ev: P) requires Minimal(Ev, ev) ensures ev(4) {
}
lemma c1(ev: P) requires Minimal(Ev, ev) ensures !ev(3) {}
lemma c2(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures ev(n + 2) {}
lemma c3(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n + 2) ensures ev(n) {}


// Finally, we "circularly" prove the equivalence among these three:
lemma a_implies_b(n: nat) requires even(n) ensures Even(n) {}
lemma b_implies_c(ev: P, n: nat) requires Minimal(Ev, ev) && Even(n) ensures ev(n) {}
lemma c_implies_a(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures even(n) {}

