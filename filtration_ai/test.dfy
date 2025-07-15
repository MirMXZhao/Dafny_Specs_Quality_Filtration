// Ported from ivy/examples/ivy/toy_consensus.ivy.

// Ivy only supports first-order logic, which is limited (perhaps in surprising
// ways). In this model of consensus, we use some tricks to model quorums in
// first-order logic without getting into the arithmetic of why sets of n/2+1
// nodes intersect.

type Node(==)
type Quorum(==)
type Choice(==)

ghost predicate Member(n: Node, q: Quorum)

// axiom: any two quorums intersect in at least one node
// SOLUTION
// note we give this without proof: this is in general dangerous! However, here
// we believe it is possible to have Node and Quorum types with this property.
//
// The way we might realize that is to have Node be a finite type (one value for
// each node in the system) and Quorum to capture any subset with strictly more
// than half the nodes. Such a setup guarantees that any two quorums intersect.
// END
lemma {:axiom} QuorumIntersect(q1: Quorum, q2: Quorum) returns (n: Node)
  ensures Member(n, q1) && Member(n, q2)

datatype Variables = Variables(
  votes: map<Node, set<Choice>>,
  // this is one reason why this is "toy" consensus: the decision is a global
  // variable rather than being decided at each node individually
  decision: set<Choice>
)
{
  ghost predicate WF()
  {}
}

datatype Step =
  | CastVoteStep(n: Node, c: Choice)
  | DecideStep(c: Choice, q: Quorum)

ghost predicate CastVote(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.CastVoteStep?
{}

ghost predicate Decide(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.DecideStep?
{}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{
}

ghost predicate Next(v: Variables, v': Variables)
{}

ghost predicate Init(v: Variables) {}

ghost predicate Safety(v: Variables) {}

// SOLUTION
ghost predicate ChoiceQuorum(v: Variables, q: Quorum, c: Choice)
  requires v.WF()
{}

ghost predicate Inv(v: Variables) {}
// END

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{}

lemma SafetyHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{}
