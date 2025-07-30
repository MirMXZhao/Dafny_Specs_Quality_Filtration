datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired
datatype Variables = Variables(
  clientCount: nat,
  server: ServerGrant, clients: seq<ClientRecord>
) {
  ghost predicate ValidIdx(idx: int) {}
  ghost predicate WellFormed() {}
}

ghost predicate Init(v:Variables) {}

ghost predicate Acquire(v:Variables, v':Variables, id:int) {}

ghost predicate Release(v:Variables, v':Variables, id:int) {}

datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {}

ghost predicate Safety(v:Variables) {}

ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{}

lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1])
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i])
  ensures behavior[|behavior|-1].WellFormed()
  ensures ClientHoldsLock(behavior[1], clientA)
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB)
{}

////////TESTS////////

method TestPseudoLiveness1() {
  var behavior := PseudoLiveness(2, 0);
  assert |behavior| >= 2;
  assert Init(behavior[0]);
  assert forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]);
  assert forall i | 0 <= i < |behavior| :: Safety(behavior[i]);
  assert behavior[|behavior|-1].WellFormed();
  assert ClientHoldsLock(behavior[1], 2);
  assert ClientHoldsLock(behavior[|behavior|-1], 0);
}

method TestPseudoLiveness2() {
  var behavior := PseudoLiveness(2, 0);
  assert |behavior| >= 2;
  assert Init(behavior[0]);
  assert forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]);
  assert forall i | 0 <= i < |behavior| :: Safety(behavior[i]);
  assert behavior[|behavior|-1].WellFormed();
  assert ClientHoldsLock(behavior[1], 2);
  assert ClientHoldsLock(behavior[|behavior|-1], 0);
}
