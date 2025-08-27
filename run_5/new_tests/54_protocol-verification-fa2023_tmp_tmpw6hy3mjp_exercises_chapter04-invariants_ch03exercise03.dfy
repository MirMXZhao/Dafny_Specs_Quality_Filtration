datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired
datatype Variables = Variables(
  clientCount: nat,
  server: ServerGrant, clients: seq<ClientRecord>
) {}


ghost predicate Init(v:Variables) {
  && v.WellFormed()
  && v.server.Unlocked?
  && |v.clients| == v.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

ghost predicate Acquire(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
  && v'.clientCount == v.clientCount
}

ghost predicate Release(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.clients[id].Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
  && v'.clientCount == v.clientCount
}

datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  case AcquireStep(id) => Acquire(v, v', id)
  case ReleaseStep(id) => Release(v, v', id)
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

ghost predicate Safety(v:Variables) {
  forall i,j |
    && 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?
    :: i == j
}

ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  && v.server == Client(clientIndex)
}

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
  var clientA := 2;
  var clientB := 0;
  var behavior := PseudoLiveness(clientA, clientB);
  assert 2 <= |behavior|;
  assert Init(behavior[0]);
  assert forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]);
  assert forall i | 0 <= i < |behavior| :: Safety(behavior[i]);
  assert behavior[|behavior|-1].WellFormed();
  assert ClientHoldsLock(behavior[1], clientA);
  assert ClientHoldsLock(behavior[|behavior|-1], clientB);
}

method TestPseudoLiveness2() {
  var clientA := 2;
  var clientB := 0;
  var behavior := PseudoLiveness(clientA, clientB);
  assert 2 <= |behavior|;
  assert Init(behavior[0]);
  assert forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]);
  assert forall i | 0 <= i < |behavior| :: Safety(behavior[i]);
  assert behavior[|behavior|-1].WellFormed();
  assert ClientHoldsLock(behavior[1], clientA);
  assert ClientHoldsLock(behavior[|behavior|-1], clientB);
}
