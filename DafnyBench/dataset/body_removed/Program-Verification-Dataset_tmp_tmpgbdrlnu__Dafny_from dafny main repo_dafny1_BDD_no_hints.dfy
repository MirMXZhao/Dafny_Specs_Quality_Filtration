// RUN: %testDafnyForEachResolver "%s"


module SimpleBDD
{
  class BDDNode
  {}
  class BDD
  {
    var root: BDDNode
    ghost predicate valid()
      reads this, Repr
    {}
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

