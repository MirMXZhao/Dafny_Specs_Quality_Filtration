datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
decreases m
{}

predicate Odd(m: Nat)
decreases m
{
    match m
        case Zero => false
        case Succ(m') => Even(m')
}


predicate Even(m: Nat)
decreases m
{
    match m
        case Zero => true
        case Succ(m') => Odd(m')
}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{}

////////TESTS////////

method TestSumMNIsEven1() {
  var m := Succ(Zero);
  var n := Succ(Zero);
  SumMNIsEven(m, n);
  assert Odd(m);
  assert Odd(n);
  assert Even(add(m, n));
}

method TestSumMNIsEven2() {
  var m := Succ(Succ(Succ(Zero)));
  var n := Succ(Succ(Succ(Succ(Succ(Zero)))));
  SumMNIsEven(m, n);
  assert Odd(m);
  assert Odd(n);
  assert Even(add(m, n));
}
