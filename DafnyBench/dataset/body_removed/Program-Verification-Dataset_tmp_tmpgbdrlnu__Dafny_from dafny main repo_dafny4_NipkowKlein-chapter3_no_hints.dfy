// RUN: %dafny /proverOpt:O:smt.qi.eager_threshold=30 /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is a Dafny encoding of chapter 3 from "Concrete Semantics: With Isabelle/HOL" by
// Tobias Nipkow and Gerwin Klein.

// ----- lists -----

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function append(xs: List, ys: List): List
{}

// ----- arithmetic expressions -----

type vname = string  // variable names
datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)  // arithmetic expressions

type val = int
type state = vname -> val

ghost function aval(a: aexp, s: state): val
{}

lemma Example0()
{}

// ----- constant folding -----

ghost function asimp_const(a: aexp): aexp
{}

lemma AsimpConst(a: aexp, s: state)
  ensures aval(asimp_const(a), s) == aval(a, s)
{}

// more constant folding

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

// The following lemma is not in the Nipkow and Klein book, but it's a fun one to prove.
lemma ASimplInvolutive(a: aexp)
  ensures asimp(asimp(a)) == asimp(a)
{
}

// ----- boolean expressions -----

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

ghost function bval(b: bexp, s: state): bool
{}

// constant folding for booleans

ghost function not(b: bexp): bexp
{}

ghost function and(b0: bexp, b1: bexp): bexp
{}

ghost function less(a0: aexp, a1: aexp): bexp
{}

ghost function bsimp(b: bexp): bexp
{}

lemma BsimpCorrect(b: bexp, s: state)
  ensures bval(bsimp(b), s) == bval(b, s)
{
/*  Here is one proof, which uses the induction hypothesis any anything smaller than b and also invokes
    the lemma AsimpCorrect on every arithmetic expression.
  forall b' | b' < b {}
  forall a {}
    Yet another possibility is to mark the lemma with {:induction b} and to use the following line in
    the body:
  forall a {}
*/
  // Here is another proof, which makes explicit the uses of the induction hypothesis and the other lemma.
  match b
  case Bc(v) =>
  case Not(b0) =>
    BsimpCorrect(b0, s);
  case And(b0, b1) =>
    BsimpCorrect(b0, s); BsimpCorrect(b1, s);
  case Less(a0, a1) =>
    AsimpCorrect(a0, s); AsimpCorrect(a1, s);
}

// ----- stack machine -----

datatype instr = LOADI(val) | LOAD(vname) | ADD

type stack = List<val>

ghost function exec1(i: instr, s: state, stk: stack): stack
{}

ghost function exec(ii: List<instr>, s: state, stk: stack): stack
{}

// ----- compilation -----

ghost function comp(a: aexp): List<instr>
{}

lemma CorrectCompilation(a: aexp, s: state, stk: stack)
  ensures exec(comp(a), s, stk) == Cons(aval(a, s), stk)
{}

lemma ExecAppend(ii0: List<instr>, ii1: List<instr>, s: state, stk: stack)
  ensures exec(append(ii0, ii1), s, stk) == exec(ii1, s, exec(ii0, s, stk))
{}

