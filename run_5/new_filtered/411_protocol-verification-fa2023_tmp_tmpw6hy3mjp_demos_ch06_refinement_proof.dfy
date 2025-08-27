module Types {}

import opened Types

module Code {}

module Spec {}

ghost predicate Inv(v: Code.Variables)
ghost function Abstraction(v: Code.Variables): Spec.Variables

lemma {:axiom} AbstractionInit(v: Code.Variables)
  requires Code.Init(v)
  ensures Inv(v)
  ensures Spec.Init(Abstraction(v))

lemma {:axiom} AbstractionInductive(v: Code.Variables, v': Code.Variables, ev: Event)
  requires Inv(v)
  requires Code.Next(v, v', ev)
  ensures Inv(v')
  ensures Spec.Next(Abstraction(v), Abstraction(v'), ev)

lemma InvAt(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires Code.Init(ss(0))
  requires forall k:nat :: Code.Next(ss(k), ss(k + 1), tr(k))
  ensures Inv(ss(i))
{}

lemma RefinementTo(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  requires forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n))
  requires forall n: nat :: Inv(ss(n))
  ensures
    var ss' := (j: nat) => Abstraction(ss(j));
    && forall n: nat | n < i :: Spec.Next(ss'(n), ss'(n + 1), tr(n))
{}

lemma Refinement(tr: nat -> Event)
  requires Code.IsBehavior(tr)
  ensures Spec.IsBehavior(tr)
{}