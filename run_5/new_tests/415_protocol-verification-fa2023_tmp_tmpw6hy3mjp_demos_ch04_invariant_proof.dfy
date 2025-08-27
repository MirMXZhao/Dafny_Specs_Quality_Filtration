type Variables
predicate Init(v: Variables)
predicate Next(v: Variables, v': Variables)

predicate Safety(v: Variables)
predicate Inv(v: Variables)

type Behavior = nat -> Variables

lemma InvHoldsTo(e: nat -> Variables, i: nat)
  requires Inv(e(0))
  requires forall i:nat :: Next(e(i), e(i+1))
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(e(i))
{}

ghost predicate IsBehavior(e: Behavior) {
  && Init(e(0))
  && forall i:nat :: Next(e(i), e(i+1))
}

lemma SafetyAlwaysHolds(e: Behavior)
  requires forall v :: Init(v) ==> Inv(v)
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  requires forall v :: Inv(v) ==> Safety(v)
  ensures IsBehavior(e) ==> forall i :: Safety(e(i))
{}

////////TESTS////////

method TestSafetyAlwaysHolds1() {
  var e: Behavior := (i: nat) => if i == 0 then Variables else Variables;
  assume forall v :: Init(v) ==> Inv(v);
  assume forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v');
  assume forall v :: Inv(v) ==> Safety(v);
  assume IsBehavior(e);
  SafetyAlwaysHolds(e);
  assert forall i :: Safety(e(i));
}

method TestSafetyAlwaysHolds2() {
  var e: Behavior := (i: nat) => Variables;
  assume forall v :: Init(v) ==> Inv(v);
  assume forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v');
  assume forall v :: Inv(v) ==> Safety(v);
  assume !IsBehavior(e);
  SafetyAlwaysHolds(e);
  assert forall i :: Safety(e(i));
}
