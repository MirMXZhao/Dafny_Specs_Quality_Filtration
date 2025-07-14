// Nim version 3: fix the bug and demonstrate a behavior.
//
// In this version, we've fixed the bug by actually flipping whose turn it is in
// each transition.

datatype Player = P1 | P2
{
  function Other(): Player {}
}
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {}

datatype Step =
  | TurnStep(take: nat, p: nat)
  | NoOpStep()

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{}

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {}

// boilerplate
lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
}

// boilerplate
ghost predicate Next(v: Variables,  v': Variables) {}

// We'll frequently prove a lemma of this form to show some example of the state
// machine transitioning. You'll prove determinism to avoid accidentally having
// transitions do things they shouldn't. Proofs will show that your state
// machine doesn't do anything bad (note this would also catch unintentional
// non-determinism, but it can be more painful to debug such issues at this
// stage). These example behaviors will prevent bugs where your state machine
// just doesn't do anything, especially because of overly restrictive
// preconditions.
lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| >= 3 // for this example, we just demonstrate there is some execution with three states
  ensures Init(b[0])
  ensures forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1])
{}

