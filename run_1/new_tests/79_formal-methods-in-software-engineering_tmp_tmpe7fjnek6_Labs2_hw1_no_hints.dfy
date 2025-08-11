datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
{}

predicate Odd(m: Nat)
{}


predicate Even(m: Nat)
{}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{}

////////TESTS////////

method TestSumMNIsEven1() {
  var m := Succ(Zero);
  var n := Succ(Succ(Succ(Zero)));
  assert Odd(m);
  assert Odd(n);
  SumMNIsEven(m, n);
  assert Even(add(m, n));
}

method TestSumMNIsEven2() {
  var m := Succ(Succ(Succ(Succ(Succ(Zero)))));
  var n := Succ(Zero);
  assert Odd(m);
  assert Odd(n);
  SumMNIsEven(m, n);
  assert Even(add(m, n));
}
