function More(x: int): int {}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{}

method ExampleLemmaUse(a: int) {}

method ExampleLemmaUse50(a: int) {}

method ExampleLemmaUse51(a: int) {}

function Ack(m: nat, n: nat): nat {}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{}

function Reduce(m: nat, x: int): int {}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  if m == 0 {
  }
  else {
    calc {
      Reduce(m, x);
    ==
      Reduce(m / 2, x + 1) - m;
    >= { ReduceLowerBound(m/2, x+1);
      x + 1 - 2 * m;
    >
      x - 2 * m;
    }
  }
}

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat
{
  match e {
    case Const(c) => c
    case Var(s) => if s in env then env[s] else 0
    case Node(op, args) => EvalList(op, args, env)
  }
}

function Unit

////////TESTS////////

method TestMore1() {
  var result := More(5);
  Increasing(5);
  assert 5 < result;
}

method TestMore2() {
  var result := More(-3);
  Increasing(-3);
  assert -3 < result;
}

method TestExampleLemmaUse1() {
  ExampleLemmaUse(10);
}

method TestExampleLemmaUse2() {
  ExampleLemmaUse(-5);
}

method TestExampleLemmaUse501() {
  ExampleLemmaUse50(100);
}

method TestExampleLemmaUse502() {
  ExampleLemmaUse50(0);
}

method TestExampleLemmaUse511() {
  ExampleLemmaUse51(42);
}

method TestExampleLemmaUse512() {
  ExampleLemmaUse51(-7);
}

method TestAck1() {
  var result := Ack(1, 3);
  Ack1n(1, 3);
  assert result == 5;
}

method TestAck2() {
  var result := Ack(1, 0);
  Ack1n(1, 0);
  assert result == 2;
}

method TestReduce1() {
  var result := Reduce(2, 10);
  ReduceUpperBound(2, 10);
  ReduceLowerBound(2, 10);
  assert result <= 10;
  assert 6 <= result;
}

method TestReduce2() {
  var result := Reduce(0, 5);
  ReduceUpperBound(0, 5);
  ReduceLowerBound(0, 5);
  assert result <= 5;
  assert 5 <= result;
}

method TestEval1() {
  var e := Const(42);
  var env := map[];
  var result := Eval(e, env);
  assert result
