function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

////////TESTS////////

method TestExpt1() {
  var res := expt(2, 3);
  assert res == 8;
}

method TestExpt2() {
  var res := expt(5, 0);
  assert res == 1;
}
