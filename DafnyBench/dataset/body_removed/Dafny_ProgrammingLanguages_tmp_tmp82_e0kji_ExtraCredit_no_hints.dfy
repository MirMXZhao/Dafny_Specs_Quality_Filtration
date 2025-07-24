datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)

function eval(e:Exp, store:map<string, int>):int
{}

//fill this function in to make optimizeFeatures work
function optimize(e:Exp):Exp
{} 

//as you write optimize this will become unproved
//you must write proof code so that Dafny can prove this
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
{

}

method optimizeFeatures()
{




	
}
