module Ex {

  datatype Variables = Variables(p1: bool, p2: bool, p3: bool, p4: bool)

  ghost predicate Init(v: Variables) {
    && !v.p1
    && !v.p2
    && !v.p3
    && !v.p4
  }

  datatype Step =
    | Step1
    | Step2
    | Step3
    | Step4
    | Noop

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      case Step1 =>
        !v.p1 && v' == v.(p1 := true)
      case Step2 =>
        v.p1 && v' == v.(p2 := true)
      case Step3 =>
        v.p2 && v' == v.(p3 := true)
      case Step4 =>
        v.p3 && v' == v.(p4 := true)
      case Noop => v' == v
    }
  }

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step: Step :: NextStep(v, v', step)
  }

  ghost predicate Safety(v: Variables)
  {
    v.p4 ==> v.p1
  }

  ghost predicate Inv(v: Variables)
  {
    && Safety(v)
    && (v.p3 ==> v.p1)
    && (v.p2 ==> v.p1)
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v) && Next(v, v')
    ensures Inv(v')
  {}

  lemma InvSafe(v: Variables)
    ensures Inv(v) ==> Safety(v)
  {
    return;
  }

  lemma SafetyHolds(v: Variables, v': Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {}

  predicate Inv2(v: Variables) {
    && (v.p2 ==> v.p1)
    && (v.p3 ==> v.p2)
    && (v.p4 ==> v.p3)
  }

  lemma Inv2Holds(v: Variables, v': Variables)
    ensures Init(v) ==> Inv2(v)
    ensures Inv2(v) && Next(v, v') ==> Inv2(v')
  {}
}

////////TESTS////////

method TestInv2Holds1() {
  var v := Variables(false, false, false, false);
  var v' := Variables(true, false, false, false);
  var initHolds := Ex.Init(v);
  var inv2Holds := Ex.Inv2(v);
  var nextHolds := Ex.Next(v, v');
  var inv2HoldsAfter := Ex.Inv2(v');
  assert initHolds ==> inv2Holds;
  assert inv2Holds && nextHolds ==> inv2HoldsAfter;
}

method TestInv2Holds2() {
  var v := Variables(true, true, false, false);
  var v' := Variables(true, true, true, false);
  var initHolds := Ex.Init(v);
  var inv2Holds := Ex.Inv2(v);
  var nextHolds := Ex.Next(v, v');
  var inv2HoldsAfter := Ex.Inv2(v');
  assert initHolds ==> inv2Holds;
  assert inv2Holds && nextHolds ==> inv2HoldsAfter;
}
