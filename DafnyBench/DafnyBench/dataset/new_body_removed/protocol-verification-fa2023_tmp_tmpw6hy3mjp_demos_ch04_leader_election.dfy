// We'll define "Between" to capture how the ring wraps around.
// SOLUTION
ghost predicate Between(start: nat, i: nat, end: nat)
{
  if start < end then start < i < end
  else i < end || start < i
}

lemma BetweenTests()
{}
// END

// ids gives each node's (unique) identifier (address)
//
// highest_heard[i] is the highest other identifier the node at index i has
// heard about (or -1 if it has heard about nobody - note that -1 is not a valid identifier).
datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {}

ghost predicate Init(v: Variables)
{
  && v.UniqueIds()
  && v.WF()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | v.ValidIdx(i) :: v.highest_heard[i] == -1)
}

ghost function max(a: int, b: int) : int {}

ghost function NextIdx(v: Variables, idx: nat) : nat
  requires v.WF()
  requires v.ValidIdx(idx)
{}

// The destination of a transmission is determined by the ring topology
datatype Step = TransmissionStep(src: nat)

// This is an atomic step where src tells its neighbor (dst, computed here) the
// highest src has seen _and_ dst updates its local state to reflect receiving
// this message.
ghost predicate Transmission(v: Variables, v': Variables, step: Step)
  requires step.TransmissionStep?
{
  var src := step.src;
  && v.WF()
  && v.ValidIdx(src)
  && v'.ids == v.ids

  // Neighbor address in ring.
  && var dst := NextIdx(v, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], v.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);

  // demo has a bug here
  // SOLUTION
  && v'.highest_heard == v.highest_heard[dst := dst_new_max]
  // END
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(_) => Transmission(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(v: Variables, i: int)
  requires v.WF()
{
  && v.ValidIdx(i)
  && v.highest_heard[i] == v.ids[i]
}

ghost predicate Safety(v: Variables)
  requires v.WF()
{
  forall i, j | IsLeader(v, i) && IsLeader(v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

// SOLUTION
ghost predicate ChordHeardDominated(v: Variables, start: nat, end: nat)
  requires v.IsChord(start, end)
  requires v.WF()
{}

// We make this opaque so Dafny does not use it automatically; instead we'll use
// the lemma UseChordDominated when needed. In many proofs opaqueness is a way
// to improve performance, since it prevents the automation from doing too much
// work; in this proof it's only so we can make clear in the proof when this
// invariant is being used.
ghost predicate {:opaque} OnChordHeardDominatesId(v: Variables)
  requires v.WF()
{}

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end )
  ensures ChordHeardDominated(v, start, end)
{}
// END


ghost predicate Inv(v: Variables)
{
  && v.WF()
     // The solution will need more conjuncts
     // SOLUTION
  && v.UniqueIds()
  && OnChordHeardDominatesId(v)
     // Safety is not needed - we can prove it holds from the other invariants
     // END
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma NextPreservesInv(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{}

lemma InvImpliesSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{}

