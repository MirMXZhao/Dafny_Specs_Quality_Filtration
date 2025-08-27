ghost predicate Between(start: nat, i: nat, end: nat)
{
  if start < end then start < i < end
  else i < end || start < i
}

datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {}

ghost predicate Init(v: Variables)
{
  && v.UniqueIds()
  && v.WF()
  && (forall i | v.ValidIdx(i) :: v.highest_heard[i] == -1)
}

ghost function max(a: int, b: int) : int {}

ghost function NextIdx(v: Variables, idx: nat) : nat
  requires v.WF()
  requires v.ValidIdx(idx)
{}

datatype Step = TransmissionStep(src: nat)

ghost predicate Transmission(v: Variables, v': Variables, step: Step)
  requires step.TransmissionStep?
{
  var src := step.src;
  && v.WF()
  && v.ValidIdx(src)
  && v'.ids == v.ids
  && var dst := NextIdx(v, src);
  && var message := max(v.highest_heard[src], v.ids[src]);
  && var dst_new_max := max(v.highest_heard[dst], message);
  && v'.highest_heard == v.highest_heard[dst := dst_new_max]
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

ghost predicate ChordHeardDominated(v: Variables, start: nat, end: nat)
  requires v.IsChord(start, end)
  requires v.WF()
{}

ghost predicate {:opaque} OnChordHeardDominatesId(v: Variables)
  requires v.WF()
{}

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end )
  ensures ChordHeardDominated(v, start, end)
{}

ghost predicate Inv(v: Variables)
{
  && v.WF()
  && v.UniqueIds()
  && OnChordHeardDominatesId(v)
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