// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<int>) {}

ghost predicate Init(c: Constants, v: Variables)
{}

function max(a: int, b: int) : int {}

function NextIdx(c: Constants, idx: nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
{}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
{}

datatype Step = TransmissionStep(srcidx: nat)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
{}

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
{}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsChord(c: Constants, v: Variables, start: int, end: int)
{}

ghost predicate Between(start: int, node: int, end: int)
{}

ghost predicate OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c)
{}

ghost predicate OnChordHeardDominatesIdInv(c: Constants, v: Variables)
{}

ghost predicate Inv(c: Constants, v: Variables)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
}

