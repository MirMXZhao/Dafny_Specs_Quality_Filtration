// RUN: %testDafnyForEachResolver "%s"


module SimpleBDD
{
  class BDDNode
  {
    static ghost predicate bitfunc(f: map<seq<bool>, bool>, n: nat)
    {}
    ghost var Contents: map<seq<bool>, bool>
    ghost var Repr: set<object>
    ghost var n: nat
    var f: BDDNode?, t: BDDNode?
    var b: bool
    ghost predicate valid()
      reads this, Repr
    {}
  }
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

