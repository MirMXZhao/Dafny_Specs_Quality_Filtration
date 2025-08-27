datatype Player = P1 | P2
{}
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn.P1?
}

datatype Step =
  | TurnStep(take: nat, p: nat)
  | NoOpStep()

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{
  var p := step.p;
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}

ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {
  match step {
    case TurnStep(_, _) => Turn(v, v', step)
    case NoOpStep() => v' == v
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
}

ghost predicate Next(v: Variables,  v': Variables) {
  exists step :: NextStep(v, v', step)
}

lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| >= 3
  ensures Init(b[0])
  ensures forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1])
{}

////////TESTS////////

method TestExampleBehavior1() {
  var b := ExampleBehavior();
  assert |b| >= 3;
  assert Init(b[0]);
  assert forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1]);
}

method TestExampleBehavior2() {
  var b := ExampleBehavior();
  assert |b| >= 3;
  assert Init(b[0]);
  assert forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1]);
}
