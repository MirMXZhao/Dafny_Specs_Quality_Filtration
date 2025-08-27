// Proving type safety of a Simply Typed Lambda-Calculus in Dafny
// adapted from Coq (http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html)

/// Utilities

// ... handy for partial functions
datatype option<A> = None | Some(get: A)

/// -----
/// Model
/// -----

/// Syntax

// Types
datatype ty =  TBase                             // (opaque base type)
            |  TArrow(T1: ty, T2: ty)            // T1 => T2
/*BOOL?
            | TBool                              // (base type for booleans)
?BOOL*/
/*NAT?
            |  TNat                              // (base type for naturals)
?NAT*/
/*REC?
            | TVar(id: int) | TRec(X: nat, T: ty)// (iso-recursive types)
?REC*/

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)
/*BOOL?
            | ttrue | tfalse                     // true, false        (boolean values)
            | tif(c: tm, a: tm, b: tm)           // if t then t else t (if expression)
?BOOL*/
/*NAT?
            | tzero | tsucc(p: tm) | tprev(n: tm)//                    (naturals)
/*BOOL?
            | teq(n1: tm, n2: tm)                //                    (equality on naturals)
?BOOL*/
?NAT*/
/*REC?
            | tfold(Tf: ty, tf: tm) | tunfold(tu: tm)//                (iso-recursive terms)
?REC*/

/// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tabs?
/*BOOL?
  || t.ttrue? || t.tfalse?
?BOOL*/
/*NAT?
  || isPeanoNumber(t)
?NAT*/
/*REC?
  || (t.tfold? && value(t.tf))
?REC*/
}

/*NAT?
predicate isPeanoNumber(t: tm)
{
  t.tzero? || (t.tsucc? && isPeanoNumber(t.p))
}
?NAT*/

// Free Variables and Substitution

function freeVariables(t: tm): set<int> //of free variables of t
{
  match t
  // interesting cases...
  case tvar(id) => {id}
  case tabs(x, T, body) => freeVariables(body)-{x}//x is bound
  // congruent cases...
  case tapp(f, arg) => freeVariables(f)+freeVariables(arg)
/*BOOL?
  case tif(c, a, b) => freeVariables(a)+freeVariables(b)+freeVariables(c)
  case ttrue => {}
  case tfalse => {}
?BOOL*/
/*NAT?
  case tzero => {}
  case tsucc(p) => freeVariables(p)
  case tprev(n) => freeVariables(n)
/*BOOL?
  case teq(n1, n2) => freeVariables(n1)+freeVariables(n2)
?BOOL*/
?NAT*/
/*REC?
  case tfold(T, t1) => freeVariables(t1)
  case tunfold(t1) => freeVariables(t1)
?REC*/
}

function substituteTermForVariable(x: int, s: tm, t: tm): tm //[x -> s]t
{
  match t
  // interesting cases...
  case tvar(x') => if x==x' then s else t
  // N.B. only capture-avoiding if s is closed...
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else substituteTermForVariable(x, s, t1))
  // congruent cases...
  case tapp(t1, t2) => tapp(substituteTermForVariable(x, s, t1), substituteTermForVariable(x, s, t2))
/*BOOL?
  case ttrue => ttrue
  case tfalse => tfalse
  case tif(t1, t2, t3) => tif(substituteTermForVariable(x, s, t1), substituteTermForVariable(x, s, t2), substituteTermForVariable(x, s, t3))
?BOOL*/
/*NAT?
  case tzero => tzero
  case tsucc(p) => tsucc(substituteTermForVariable(x, s, p))
  case tprev(n) => tprev(substituteTermForVariable(x, s, n))
/*BOOL?
  case teq(n1, n2) => teq(substituteTermForVariable(x, s, n1), substituteTermForVariable(x, s, n2))
?BOOL*/
?NAT*/
/*REC?
  case tfold(T, t1) => tfold(T, substituteTermForVariable(x, s, t1))
  case tunfold(t1) => tunfold(substituteTermForVariable(x, s, t1))
?REC*/
}

/*REC?
function freeTypeVariables(T: ty): set<int> //of free type variables of T
{
  match T
  case TVar(X) => {X}
  case TRec(X, T1) => freeTypeVariables(T1)-{X}
  case TArrow(T1, T2) => freeTypeVariables(T1)+freeTypeVariables(T2)
  case TBase => {}
/*BOOL?
  case TBool => {}
?BOOL*/
/*NAT?
  case TNat => {}
?NAT*/
}

function substituteTypeForTypeVariable(X: int, S: ty, T: ty): ty
{
  match T
  case TVar(X') => if X==X' then S else T
  case TRec(X', T1) => TRec(X', if X==X' then T1 else substituteTypeForTypeVariable(X, S, T1))
  case TArrow(T1, T2) => TArrow(substituteTypeForTypeVariable(X, S, T1), substituteTypeForTypeVariable(X, S, T2))
  case TBase => TBase
/*BOOL?
  case TBool => TBool
?BOOL*/
/*NAT?
  case TNat => TNat
?NAT*/
}

predicate isClosedType(T: ty)
{
  forall x :: x !in freeTypeVariables(T)
}
?REC*/

// Reduction
function evaluateOneStep(t: tm): option<tm>
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then
  Some(substituteTermForVariable(t.f.x, t.arg, t.f.body))
  /* App1 */       else if (t.tapp? && evaluateOneStep(t.f).Some?) then
  Some(tapp(evaluateOneStep(t.f).get, t.arg))
  /* App2 */       else if (t.tapp? && value(t.f) && evaluateOneStep(t.arg).Some?) then
  Some(tapp(t.f, evaluateOneStep(t.arg).get))
/*BOOL?
  /* IfTrue */     else if (t.tif? && t.c == ttrue) then
  Some(t.a)
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then
  Some(t.b)
  /* If */         else if (t.tif? && evaluateOneStep(t.c).Some?) then
  Some(tif(evaluateOneStep(t.c).get, t.a, t.b))
?BOOL*/
/*NAT?
  /* Prev0 */
                   else if (t.tprev? && t.n.tzero?) then
  Some(tzero)
  /* PrevSucc */   else if (t.tprev? && isPeanoNumber(t.n) && t.n.tsucc?) then
  Some(t.n.p)
  /* Prev */       else if (t.tprev? && evaluateOneStep(t.n).Some?) then
  Some(tprev(evaluateOneStep(t.n).get))
  /* Succ */       else if (t.tsucc? && evaluateOneStep(t.p).Some?) then
  Some(tsucc(evaluateOneStep(t.p).get))
/*BOOL?
  /* EqTrue0 */    else if (t.teq? && t.n1.tzero? && t.n2.tzero?) then
  Some(ttrue)
  /* EqFalse1 */   else if (t.teq? && t.n1.tsucc? && isPeanoNumber(t.n1) && t.n2.tzero?) then
  Some(tfalse)
  /* EqFalse2 */   else if (t.teq? && t.n1.tzero? && t.n2.tsucc? && isPeanoNumber(t.n2)) then
  Some(tfalse)
  /* EqRec */      else if (t.teq? && t.n1.tsucc? && t.n2.tsucc? && isPeanoNumber(t.n1) && isPeanoNumber(t.n2)) then
  Some(teq(t.n1.p, t.n2.p))
  /* Eq1 */        else if (t.teq? && evaluateOneStep(t.n1).Some?) then
  Some(teq(evaluateOneStep(t.n1).get, t.n2))
  /* Eq2 */        else if (t.teq? && isPeanoNumber(t.n1) && evaluateOneStep(t.n2).Some?) then
  Some(teq(t.n1, evaluateOneStep(t.n2).get))
?BOOL*/
?NAT*/
/*REC?
  /* UnfoldFold */ else if (t.tunfold? && t.tu.tfold? && value(t.tu.tf)) then Some(t.tu.tf)
  /* Fold */       else if (t.tfold? && evaluateOneStep(t.tf).Some?) then Some(tfold(t.Tf, evaluateOneStep(t.tf).get))
  /* Unfold */     else if (t.tunfold? && evaluateOneStep(t.tu).Some?) then Some(tunfold(evaluateOneStep(t.tu).get))
?REC*/
  else None
}

// Multistep reduction:
// The term t reduces to the term t' in n or less number of steps.
predicate evaluatesToInSteps(t: tm, t': tm, n: nat)
  decreases n;
{
  t == t' || (n > 0 && evaluateOneStep(t).Some? && evaluatesToInSteps(evaluateOneStep(t).get, t', n-1))
}

// Examples
lemma lemma_step_example1(n: nat)
  requires n > 0;
  // (\x:B=>B.x) (\x:B.x) reduces to (\x:B.x)
  ensures evaluatesToInSteps(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
}


/// Typing

// A context is a partial map from variable names to types.
function lookupVariableType(c: map<int,ty>, x: int): option<ty>
{
  if (x in c) then Some(c[x]) else None
}
function extendContext(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x:=T]
}

// Typing Relation
function inferType(c: map<int,ty>, t: tm): option<ty>
  decreases t;
{
  match t
  /* Var */  case tvar(id) => lookupVariableType(c, id)
  /* Abs */  case tabs(x, T, body) =>
  var ty_body := inferType(extendContext(x, T, c), body);
                     if (ty_body.Some?) then
  Some(TArrow(T, ty_body.get))          else None
  /* App */  case tapp(f, arg) =>
  var ty_f   := inferType(c, f);
  var ty_arg := inferType(c, arg);
                     if (ty_f.Some? && ty_arg.Some?) then
  if ty_f.get.TArrow? && ty_f.get.T1 == ty_arg.get then
  Some(ty_f.get.T2)  else None else None
/*BOOL?
  /* True */  case ttrue => Some(TBool)
  /* False */ case tfalse => Some(TBool)
  /* If */    case tif(cond, a, b) =>
  var ty_c := inferType(c, cond);
  var ty_a := inferType(c, a);
  var ty_b := inferType(c, b);
                     if (ty_c.Some? && ty_a.Some? && ty_b.Some?) then
  if ty_c.get == TBool && ty_a.get == ty_b.get then
  ty_a
                     else None else None
?BOOL*/
/*NAT?
  /* Zero */  case tzero => Some(TNat)
  /* Prev */  case tprev(n) =>
  var ty_n := inferType(c, n);
                     if (ty_n.Some?) then
  if ty_n.get == TNat then
  Some(TNat)         else None else None
  /* Succ */  case tsucc(p) =>
  var ty_p := inferType(c, p);
                     if (ty_p.Some?) then
  if ty_p.get == TNat then
  Some(TNat)         else None else None
/*BOOL?
  /* Eq */    case teq(n1, n2) =>
  var ty_n1 := inferType(c, n1);
  var ty_n2 := inferType(c, n2);
                      if (ty_n1.Some? && ty_n2.Some?) then
  if ty_n1.get == TNat && ty_n2.get == TNat then
  Some(TBool)         else None else None
?BOOL*/
?NAT*/
/*REC?
  /* Fold */  case tfold(U, t1) =>
  var ty_t1 := if (isClosedType(U)) then inferType(c, t1) else None;
                      if (ty_t1.Some?) then
  if U.TRec? && ty_t1.get==substituteTypeForTypeVariable(U.X, U, U.T) then
  Some(U)             else None else None
  /* Unfold */ case tunfold(t1) =>
  var ty_t1 := inferType(c, t1);
                      if ty_t1.Some? then
  var U := ty_t1.get;
  if U.TRec? then
  Some(substituteTypeForTypeVariable(U.X, U, U.T)) else None else None
?REC*/
}

// Examples

lemma example_typing_1()
  ensures inferType(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
}

lemma example_typing_2()
  ensures inferType(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{
  var c := extendContext(1, TArrow(TBase, TBase), extendContext(0, TBase, map[]));
  assert lookupVariableType(c, 0) == Some(TBase);
  assert inferType(c, tvar(0)) == Some(TBase);
  assert inferType(c, tvar(1)) == Some(TArrow(TBase, TBase));
  assert inferType(c, tapp(tvar(1), tapp(tvar(1), tvar(0)))) == Some(TBase);
}

lemma nonexample_typing_1()
  ensures inferType(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
{
  var c := extendContext(1, TBase, extendContext(0, TBase, map[]));
  assert lookupVariableType(c, 0) == Some(TBase);
  assert inferType(c, tapp(tvar(0), tvar(1))) == None;
}

lemma nonexample_typing_3(S: ty, T: ty)
  ensures inferType(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{
  var c := extendContext(0, S, map[]);
  assert inferType(c, tapp(tvar(0), tvar(0))) == None;
}

/*BOOL?
lemma example_typing_bool()
  ensures inferType(map[], tabs(0, TBase, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))))) ==
          Some(TArrow(TBase, TArrow(TBase, TArrow(TBool, TBase))));
{
  var c0 := extendContext(0, TBase, map[]);
  var c1 := extendContext(1, TBase, c0);
  var c2 := extendContext(2, TBool, c1);
  assert inferType(c2, tvar(2)) == Some(TBool);
  assert inferType(c2, tvar(1)) == Some(TBase);
  assert inferType(c2, tvar(0)) == Some(TBase);
  assert inferType(c2, tif(tvar(2), tvar(0), tvar(1))) == Some(TBase);
  assert inferType(c1, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))) == Some(TArrow(TBool, TBase));
  assert inferType(c0, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1))))) == Some(TArrow(TBase, TArrow(TBool, TBase)));
}
?BOOL*/

/*NAT?
lemma example_typing_nat()
  ensures inferType(map[], tabs(0, TNat, tprev(tvar(0)))) == Some(TArrow(TNat, TNat));
{
  var c := extendContext(0, TNat, map[]);
  assert inferType(c, tprev(tvar(0)))==Some(TNat);
}
?NAT*/

/*REC?
// TODO
lemma example_typing_rec()
  // ∅ |- foldµT. T→α(λx : µT. T → α. (unfold x) x) : µT. T → α
  ensures inferType(map[], tfold(TRec(0, TArrow(TVar(0), TBase)), tabs(0, TRec(0, TArrow(TVar(0), TBase)), tapp(tunfold(tvar(0)), tvar(0))))) ==
          Some(TRec(0, TArrow(TVar(0), TBase)));
{
  var R := TRec(0, TArrow(TVar(0), TBase));
  var c := extendContext(0, R, map[]);
  //{x : µT. T → α}  x : µT. T → α
  assert inferType(c, tvar(0)) == Some(R);
  //{x : µT. T → α}  (unfold x):(µT. T → α) → α {x : µT. T → α}  x : µT. T → α
  assert substituteTypeForTypeVariable(R.X, R, R.T) == TArrow(R, TBase);
  assert inferType(c, tunfold(tvar(0))) == Some(TArrow(R, TBase));
  //{x : µT. T → α}  ( (unfold x) x)) : α
  assert inferType(c, tapp(tunfold(tvar(0)), tvar(0))) == Some(TBase);
  //∅  (λx : µT. T → α. (unfold x) x)) :(µT. T → α) → α
  assert inferType(map[], tabs(0, R, tapp(tunfold(tvar(0)), tvar(0)))) == Some(TArrow(R, TBase));
  assert freeTypeVariables(R)==freeTypeVariables(TArrow(TVar(0),TBase))-{0}=={};
  assert isClosedType(R);
  assert inferType(map[], tfold(TRec(0, TArrow(TVar(0), TBase)), tabs(0, TRec(0, TArrow(TVar(0), TBase)), tapp(tunfold(tvar(0)), tvar(0))))).Some?;
}
?REC*/

/// -----------------------
/// Type-Safety Properties
/// -----------------------

// Progress:
// A well-typed term is either a value or it can step.
lemma theorem_progress(t: tm)
  requires inferType(map[], t).Some?;
  ensures value(t) || evaluateOneStep(t).Some?;
{
}

// Towards preservation and the substitution lemma

// If x is free in t and t is well-typed in some context,
// then this context must contain x.
lemma {:induction c, t} lemma_freeVariableInTypingContext(c: map<int,ty>, x: int, t: tm)
  requires x in freeVariables(t);
  requires inferType(c, t).Some?;
  ensures lookupVariableType(c, x).Some?;
  decreases t;
{
}

// A closed term does not contain any free variables.
// N.B. We're only interested in proving type soundness of closed terms.
predicate isClosedTerm(t: tm)
{
  forall x :: x !in freeVariables(t)
}

// If a term can be well-typed in an empty context,
// then it is closed.
lemma corollary_typableInEmptyContext_impliesClosedTerm(t: tm)
  requires inferType(map[], t).Some?;
  ensures isClosedTerm(t);
{
  forall (x:int) ensures x !in freeVariables(t);
  {
    if (x in freeVariables(t)) {
      lemma_freeVariableInTypingContext(map[], x, t);
      assert false;
    }
  }
}

// If a term t is well-typed in context c,
//    and context c' agrees with c on all free variables of t,
// then the term t is well-typed in context c',
//      with the same type as in context c.
lemma {:induction t} lemma_typingContextInvariance(c: map<int,ty>, c': map<int,ty>, t: tm)
  requires inferType(c, t).Some?;
  requires forall x: int :: x in freeVariables(t) ==> lookupVariableType(c, x) == lookupVariableType(c', x);
  ensures inferType(c, t) == inferType(c', t);
  decreases t;
{
  if (t.tabs?) {
    assert freeVariables(t.body) == freeVariables(t) || freeVariables(t.body) == freeVariables(t) + {t.x};
    lemma_typingContextInvariance(extendContext(t.x, t.T, c), extendContext(t.x, t.T, c'), t.body);
  }
}

// Substitution preserves typing:
// If  s has type S in an empty context,
// and t has type T in a context extended with x having type S,
// then [x -> s]t has type T as well.
lemma lemma_substitutionPreservesTyping(c: map<int,ty>, x: int, s: tm, t: tm)
  requires inferType(map[], s).Some?;
  requires inferType(extendContext(x, inferType(map[], s).get, c), t).Some?;
  ensures inferType(c, substituteTermForVariable(x, s, t)) == inferType(extendContext(x, inferType(map[], s).get, c), t);
  decreases t;
{
  var S := inferType(map[], s).get;
  var cs := extendContext(x, S, c);
  var T  := inferType(cs, t).get;

  if (t.tvar?) {
    if (t.id==x) {
      assert T == S;
      corollary_typableInEmptyContext_impliesClosedTerm(s);
      lemma_typingContextInvariance(map[], c, s);
    }
  }
  if (t.tabs?) {
    if (t.x==x) {
      lemma_typingContextInvariance(cs, c, t);
    } else {
      var cx  := extendContext(t.x, t.T, c);
      var csx := extendContext(x, S, cx);
      var cxs := extendContext(t.x, t.T, cs);
      lemma_typingContextInvariance(cxs, csx, t.body);
      lemma_substitutionPreservesTyping(cx, x, s, t.body);
    }
  }
}


// Preservation:
// A well-type term which steps preserves its type.
lemma theorem_preservation(t: tm)
  requires inferType(map[], t).Some?;
  requires evaluateOneStep(t).Some?;
  ensures inferType(map[], evaluateOneStep(t).get) == inferType(map[], t);
{
  if (t.tapp? && value(t.f) && value(t.arg)) {
    lemma_substitutionPreservesTyping(map[], t.f.x, t.arg, t.f.body);
  }
}

// A normal form cannot step.
predicate isNormalForm(t: tm)
{
  evaluateOneStep(t).None?
}

// A stuck term is a normal form that is not a value.
predicate isStuckTerm(t: tm)
{
  isNormalForm(t) && !value(t)
}

// Type soundness:
// A well-typed term cannot be stuck.
lemma corollary_typeSoundness(t: tm, t': tm, T: ty, n: nat)
  requires inferType(map[], t) == Some(T);
  requires evaluatesToInSteps(t, t', n);
  ensures !isStuckTerm(t');
  decreases n;
{
  theorem_progress(t);
  if (t != t') {
   theorem_preservation(t);
   corollary_typeSoundness(evaluateOneStep(t).get, t', T, n-1);
  }
}

/// QED