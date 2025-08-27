datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)

function eval(e:Exp, store:map<string, int>):int
{}

function optimize(e:Exp):Exp
{} 

method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
{

}

////////TESTS////////

method TestOptimizeCorrect1() {
  var e := Plus(Const(3), Const(5));
  var s := map["x" := 2, "y" := 7];
  optimizeCorrect(e, s);
  assert eval(e, s) == eval(optimize(e), s);
}

method TestOptimizeCorrect2() {
  var e := Mult(Var("x"), Plus(Const(0), Var("y")));
  var s := map["x" := 4, "y" := 3];
  optimizeCorrect(e, s);
  assert eval(e, s) == eval(optimize(e), s);
}
