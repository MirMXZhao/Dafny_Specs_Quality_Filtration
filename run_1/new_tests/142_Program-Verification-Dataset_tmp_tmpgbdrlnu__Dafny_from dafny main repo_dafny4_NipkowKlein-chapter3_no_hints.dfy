datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function append(xs: List, ys: List): List
{}

type vname = string
datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)

type val = int
type state = vname -> val

ghost function aval(a: aexp, s: state): val
{}

lemma Example0()
{}

ghost function asimp_const(a: aexp): aexp
{}

lemma AsimpConst(a: aexp, s: state)
  ensures aval(asimp_const(a), s) == aval(a, s)
{}

ghost function plus(a0: aexp, a1: aexp): aexp
{}

lemma AvalPlus(a0: aexp, a1: aexp, s: state)
  ensures aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s)
{}

ghost function asimp(a: aexp): aexp
{}

lemma AsimpCorrect(a: aexp, s: state)
  ensures aval(asimp(a), s) == aval(a, s)
{}

lemma ASimplInvolutive(a: aexp)
  ensures asimp(asimp(a)) == asimp(a)
{
}

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

ghost function bval(b: bexp, s: state): bool
{}

ghost function not(b: bexp): bexp
{}

ghost function and(b0: bexp, b1: bexp): bexp
{}

ghost function less(a0: aexp, a1: aexp): bexp
{}

ghost function bsimp(b: bexp): bexp
{}

lemma BsimpCorrect(b: bexp, s: state)
  ensures bval(bsimp(

////////TESTS////////

method TestBsimp1() {
  var b := And(Bc(true), Less(N(5), N(10)));
  var s := (x: vname) => 0;
  var result := bsimp(b);
  assert bval(result, s) == bval(b, s);
}

method TestBsimp2() {
  var b := Not(And(Bc(false), Less(V("x"), N(0))));
  var s := (x: vname) => if x == "x" then 5 else 0;
  var result := bsimp(b);
  assert bval(result, s) == bval(b, s);
}
