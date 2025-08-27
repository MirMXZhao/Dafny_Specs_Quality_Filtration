function More(x: int): int {}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{}

method ExampleLemmaUse(a: int) {}

// Ex 5.0
method ExampleLemmaUse50(a: int) {}

// Ex 5.1
method ExampleLemmaUse51(a: int) {}

// Ex 5.6
function Ack(m: nat, n: nat): nat {}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{}

// Ex 5.5
function Reduce(m: nat, x: int): int {}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{}

// 5.5.1
lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{}


// ------------------------------------------------------------------------------
// ----- Expr Eval --------------------------------------------------------------
// ------------------------------------------------------------------------------

// 5.8.0

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat
{}

// intro'd in 5.8.1
function Unit(op: Op): nat {}

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
  decreases args, op, env
{}

function Substitute(e: Expr, n: string, c: nat): Expr
{}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{}

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
  decreases args, op, n, c, env
{}

// Ex 5.16
lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
{}

lemma EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  decreases es, op, n, env
  requires n in env.Keys
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
{}

// Ex 5.17
lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{}

lemma EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  decreases args, op, n, env
  requires n !in env.Keys
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
{}

// Ex 5.18
lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
{}

lemma SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
{}

// 5.8.1
// Optimization is correct

function Optimize(e: Expr): Expr
  // intrinsic
  // ensures forall env: map<string, nat> :: Eval(Optimize(e), env) == Eval(e, env)
{}

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env)
{}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
  // intrinsic
  // ensures forall op: Op, env: map<string, nat> :: u == Unit(op) ==> Eval(Node(op, OptimizeAndFilter(args, u)), env) == Eval(Node(op, args), env)
{}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env) == Eval(Node(op, args), env)
{}

lemma EvalListUnitHead(head: Expr, tail: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(head, env) == Unit(op) ==> EvalList(op, Cons(head, tail), env) == EvalList(op, tail, env)
{}

function Shorten(op: Op, args: List<Expr>): Expr {}

lemma ShortenCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
{}
