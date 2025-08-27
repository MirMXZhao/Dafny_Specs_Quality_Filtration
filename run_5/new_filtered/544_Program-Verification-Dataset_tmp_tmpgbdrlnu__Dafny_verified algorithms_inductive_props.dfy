ghost predicate even(n: nat) {
  match n {
    case 0 => true
    case 1 => false
    case _ => even(n - 2)
  }
}

lemma a0() ensures even(4) {}
lemma a1() ensures !even(3) {}
lemma a2(n: nat) requires even(n) ensures even(n + 2) {}
lemma a3(n: nat) requires even(n + 2) ensures even(n) {}

datatype EvenRule =
  | ev_0
  | ev_SS(r: EvenRule)
{}
ghost predicate Even(n: nat) {
  exists r: EvenRule :: r.apply() == n
}

lemma b0() ensures Even(4) {}
lemma b1() ensures !Even(3) {}
lemma b2(n: nat) requires Even(n) ensures Even(n + 2) {}
lemma b3(n: nat) requires Even(n + 2) ensures Even(n) {}

type P = nat -> bool
ghost predicate Ev(ev: P) {
  && ev(0)
  && (forall n: nat | ev(n) :: ev(n + 2))
}

ghost predicate Minimal(Ev: P -> bool, ev: P) {
  && Ev(ev)
  && (forall ev': P, n: nat | Ev(ev') :: ev(n) ==> ev'(n))
}

lemma c0(ev: P) requires Minimal(Ev, ev) ensures ev(4) {
  assert ev(2);
}
lemma c1(ev: P) requires Minimal(Ev, ev) ensures !ev(3) {}
lemma c2(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures ev(n + 2) {}
lemma c3(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n + 2) ensures ev(n) {}

lemma a_implies_b(n: nat) requires even(n) ensures Even(n) {}
lemma b_implies_c(ev: P, n: nat) requires Minimal(Ev, ev) && Even(n) ensures ev(n) {}
lemma c_implies_a(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures even(n) {}