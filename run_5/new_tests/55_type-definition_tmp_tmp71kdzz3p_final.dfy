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

type Env = map<VarName, Type>

predicate hasType(gamma: Env, e: Exp, t: Type)
{
    match e {

        case Var(x) =>  x in gamma && t == gamma[x]
        case Lam(x, t, e) => hasType(gamma, e, t)
        case App(e1,e2) => hasType(gamma, e1, t) && hasType(gamma, e2, t)
        case True() => t == Bool
        case False() => t == Bool
        case Cond(e0, e1, e2) => hasType(gamma, e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t)
    }    
}

////////TESTS////////

method TestFV1() {
    var e := App(Var("x"), Lam("y", Int, Var("z")));
    var result := FV(e);
    assert result == {"x", "z"};
}

method TestFV2() {
    var e := Cond(Var("a"), True(), Lam("b", Bool, Var("b")));
    var result := FV(e);
    assert result == {"a"};
}
