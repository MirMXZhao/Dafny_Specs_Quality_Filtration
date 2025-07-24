// -------------------------------------------------------------
// 1. Implementing type inference
// -------------------------------------------------------------

// Syntax:
//
// τ := Int | Bool | τ1->τ2
// e ::= x | λx : τ.e | true| false| e1 e2 | if e then e1 else e2
// v ::= true | false | λx : τ.e
// E ::= [·] | E e | v E | if E then e1 else e2
type VarName = string

type TypeVar = Type -> Type

datatype Type = Int | Bool | TypeVar

datatype Exp =
    | Var(x: VarName)
    | Lam(x: VarName, t: Type, e: Exp)
    | App(e1: Exp, e2:Exp)
    | True()
    | False()
    | Cond(e0: Exp, e1: Exp, e2: Exp)

datatype Value =
    | TrueB()
    | FalseB()
    | Lam(x: VarName, t: Type, e: Exp)

datatype Eva = 
    | E()
    | EExp(E : Eva, e : Exp)
    | EVar(v : Value, E : Eva)
    | ECond(E:Eva, e1 : Exp, e2 : Exp)

function FV(e: Exp): set<VarName> {}
// Typing rules system
// -------------------------------------------------------------
// Typing rules system
type Env = map<VarName, Type>

predicate hasType(gamma: Env, e: Exp, t: Type)
{}

// -----------------------------------------------------------------
// 2. Extending While with tuples
// -----------------------------------------------------------------


/*lemma {:induction false} extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma, e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma[x1 := t1], e, t)
{}    
