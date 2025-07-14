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
{}

/*NAT?
predicate peano(t: tm)
{}
?NAT*/

// Free Variables and Substitution

function fv(t: tm): set<int> //of free variables of t
{}

function subst(x: int, s: tm, t: tm): tm //[x -> s]t
{}

/*REC?
function ty_fv(T: ty): set<int> //of free type variables of T
{}

function tsubst(X: int, S: ty, T: ty): ty
{}

predicate ty_closed(T: ty)
{}
?REC*/

// Reduction
function step(t: tm): option<tm>
{}

// Multistep reduction:
// The term t reduces to the term t' in n or less number of steps.
predicate reduces_to(t: tm, t': tm, n: nat)
{}

// Examples
lemma lemma_step_example1(n: nat)
  requires n > 0;
  // (\x:B=>B.x) (\x:B.x) reduces to (\x:B.x)
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
}


/// Typing

// A context is a partial map from variable names to types.
function find(c: map<int,ty>, x: int): option<ty>
{}
function extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x:=T]
}

// Typing Relation
function has_type(c: map<int,ty>, t: tm): option<ty>
{}

// Examples

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
}

lemma example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{}

lemma nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
{}

lemma nonexample_typing_3(S: ty, T: ty)
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{}

/*BOOL?
lemma example_typing_bool()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))))) ==
          Some(TArrow(TBase, TArrow(TBase, TArrow(TBool, TBase))));
{}
?BOOL*/

/*NAT?
lemma example_typing_nat()
  ensures has_type(map[], tabs(0, TNat, tprev(tvar(0)))) == Some(TArrow(TNat, TNat));
{}
?NAT*/

/*REC?
// TODO
lemma example_typing_rec()
  // ∅ |- foldµT. T→α(λx : µT. T → α. (unfold x) x) : µT. T → α
  ensures has_type(map[], tfold(TRec(0, TArrow(TVar(0), TBase)), tabs(0, TRec(0, TArrow(TVar(0), TBase)), tapp(tunfold(tvar(0)), tvar(0))))) ==
          Some(TRec(0, TArrow(TVar(0), TBase)));
{}
?REC*/

/// -----------------------
/// Type-Safety Properties
/// -----------------------

// Progress:
// A well-typed term is either a value or it can step.
lemma theorem_progress(t: tm)
  requires has_type(map[], t).Some?;
  ensures value(t) || step(t).Some?;
{
}

// Towards preservation and the substitution lemma

// If x is free in t and t is well-typed in some context,
// then this context must contain x.
lemma {:induction c, t} lemma_free_in_context(c: map<int,ty>, x: int, t: tm)
  requires x in fv(t);
  requires has_type(c, t).Some?;
  ensures find(c, x).Some?;
{
}

// A closed term does not contain any free variables.
// N.B. We're only interested in proving type soundness of closed terms.
predicate closed(t: tm)
{}

// If a term can be well-typed in an empty context,
// then it is closed.
lemma corollary_typable_empty__closed(t: tm)
  requires has_type(map[], t).Some?;
  ensures closed(t);
{
  forall (x:int) ensures x !in fv(t);
  {
    if (x in fv(t)) {
      lemma_free_in_context(map[], x, t);
    }
  }
}

// If a term t is well-typed in context c,
//    and context c' agrees with c on all free variables of t,
// then the term t is well-typed in context c',
//      with the same type as in context c.
lemma {:induction t} lemma_context_invariance(c: map<int,ty>, c': map<int,ty>, t: tm)
  requires has_type(c, t).Some?;
  requires forall x: int :: x in fv(t) ==> find(c, x) == find(c', x);
  ensures has_type(c, t) == has_type(c', t);
{
  if (t.tabs?) {
    lemma_context_invariance(extend(t.x, t.T, c), extend(t.x, t.T, c'), t.body);
  }
}

// Substitution preserves typing:
// If  s has type S in an empty context,
// and t has type T in a context extended with x having type S,
// then [x -> s]t has type T as well.
lemma lemma_substitution_preserves_typing(c: map<int,ty>, x: int, s: tm, t: tm)
  requires has_type(map[], s).Some?;
  requires has_type(extend(x, has_type(map[], s).get, c), t).Some?;
  ensures has_type(c, subst(x, s, t)) == has_type(extend(x, has_type(map[], s).get, c), t);
{
  var S := has_type(map[], s).get;
  var cs := extend(x, S, c);
  var T  := has_type(cs, t).get;

  if (t.tvar?) {
    if (t.id==x) {
      corollary_typable_empty__closed(s);
      lemma_context_invariance(map[], c, s);
    }
  }
  if (t.tabs?) {
    if (t.x==x) {
      lemma_context_invariance(cs, c, t);
    } else {
      var cx  := extend(t.x, t.T, c);
      var csx := extend(x, S, cx);
      var cxs := extend(t.x, t.T, cs);
      lemma_context_invariance(cxs, csx, t.body);
      lemma_substitution_preserves_typing(cx, x, s, t.body);
    }
  }
}


// Preservation:
// A well-type term which steps preserves its type.
lemma theorem_preservation(t: tm)
  requires has_type(map[], t).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get) == has_type(map[], t);
{
  if (t.tapp? && value(t.f) && value(t.arg)) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.body);
  }
}

// A normal form cannot step.
predicate normal_form(t: tm)
{
  step(t).None?
}

// A stuck term is a normal form that is not a value.
predicate stuck(t: tm)
{}

// Type soundness:
// A well-typed term cannot be stuck.
lemma corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t) == Some(T);
  requires reduces_to(t, t', n);
  ensures !stuck(t');
{}

/// QED
