module Ints {}

module Lang {}

/* Well-formed check: offsets are all within the program */
/* Main safety property: additions do not overflow */

/* First, we give the concrete semantics of programs. */

module ConcreteEval {
  import opened Ints
  import opened Lang

  type State = Reg -> u32

  function update_state(s: State, r0: Reg, v: u32): State {}

  datatype Option<T> = Some(v: T) | None

  function expr_eval(env: State, e: Expr): Option<u32>
  {}

  // stmt_step executes a single statement
  //
  // Returns a new state and a relative PC offset (which is 1 for non-jump
  // statements).
  function stmt_step(env: State, s: Stmt): Option<(State, int)> {}

  datatype ExecResult = Ok(env: State) | NoFuel | Error

  // Run a program starting at pc.
  //
  // The sequence of statements is constant, meant to reflect a static program.
  // Termination occurs if the pc ever reaches exactly the end.
  //
  // Errors can come from either executing statements (see stmt_step for those
  // errors), or from an out-of-bounds pc (negative or not past the end of ss).
  //
  // fuel is needed to make this function terminate; the idea is that if there
  // exists some fuel that makes the program terminate, that is it's complete
  // execution, and if it always runs out of fuel it has an infinite loop.
  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
  {}

}

/* Now we turn to analyzing programs */

module AbstractEval {
  import opened Ints
  import opened Lang

  datatype Val = Interval(lo: int, hi: int)

  datatype AbstractState = AbstractState(rs: Reg -> Val)

  function expr_eval(env: AbstractState, e: Expr): Val {}

  function update_state(env: AbstractState, r0: Reg, v: Val): AbstractState {}

  // function stmt_step(env: State, s: Stmt): Option<(State, int)>
  function stmt_eval(env: AbstractState, s: Stmt): (AbstractState, set<int>) {}

  /* TODO(tej): to interpret a program, we need to explore all paths. Along the
   * way, we would have to look for loops - our plan is to disallow them (unlike
   * a normal abstract interpretation which would try to run till a fixpoint). */

  // Implement a check for just the jump targets, which are static and thus
  // don't even need abstract interpretation.

  // Check that jump targets ss[from..] are valid.
  function has_valid_jump_targets(ss: seq<Stmt>, from: nat): bool
    requires from <= |ss|
  {}

  ghost predicate valid_jump_targets(ss: seq<Stmt>) {}

  lemma has_valid_jump_targets_ok_helper(ss: seq<Stmt>, from: nat)
    requires from <= |ss|
    ensures has_valid_jump_targets(ss, from) <==>
            (forall i | from <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|)
  {
  }

  lemma has_valid_jump_targets_ok(ss: seq<Stmt>)
    ensures has_valid_jump_targets(ss, 0) <==> valid_jump_targets(ss)
  {}
}

module AbstractEvalProof {
  import opened Ints
  import opened Lang
  import E = ConcreteEval
  import opened AbstractEval

  /* What does it mean for a concrete state to be captured by an abstract state?
   * (Alternately, interpret each abstract state as a set of concrete states) */

  ghost predicate reg_included(c_v: u32, v: Val) {}

  ghost predicate state_included(env: E.State, abs: AbstractState) {}

  lemma expr_eval_ok(env: E.State, abs: AbstractState, e: Expr)
    requires state_included(env, abs)
    requires E.expr_eval(env, e).Some?
    ensures reg_included(E.expr_eval(env, e).v, expr_eval(abs, e))
  {}

  lemma stmt_eval_ok(env: E.State, abs: AbstractState, stmt: Stmt)
    requires state_included(env, abs)
    requires E.stmt_step(env, stmt).Some?
    ensures state_included(E.stmt_step(env, stmt).v.0, stmt_eval(abs, stmt).0)
  {}
}

