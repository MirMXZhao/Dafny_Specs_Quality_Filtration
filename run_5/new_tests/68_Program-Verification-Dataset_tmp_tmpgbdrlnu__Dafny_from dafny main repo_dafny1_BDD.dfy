module SimpleBDD
{
  class BDDNode
  {}
  class BDD
  {
    var root: BDDNode
    ghost predicate valid()
      reads this, Repr
    {
      root in Repr && root.Repr <= Repr && root.valid() &&
      n == root.n && Contents == root.Contents
    }
    constructor () {}

    ghost var Contents: map<seq<bool>, bool>
    var n: nat
    ghost var Repr: set<object>

    method Eval(s: seq<bool>) returns(b: bool)
      requires valid() && |s| == n
      ensures b == Contents[s]
    {}
  }
}

////////TESTS////////

method TestEval1() {
  var bdd := new BDD();
  var s := [true, false, true];
  var b := bdd.Eval(s);
  assert b == bdd.Contents[s];
}

method TestEval2() {
  var bdd := new BDD();
  var s := [false, false];
  var b := bdd.Eval(s);
  assert b == bdd.Contents[s];
}
