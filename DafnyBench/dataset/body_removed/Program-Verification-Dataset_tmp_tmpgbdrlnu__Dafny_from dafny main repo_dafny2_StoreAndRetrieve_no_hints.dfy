// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// This file shows an example program that uses both refinement and :autocontracts
// specify a class that stores a set of things that can be retrieved using a query.
//
// (For another example that uses these features, see Test/dafny3/CachedContainer.dfy.)

abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>
    ghost predicate Valid() {}
    ghost predicate {} Valid'()
      reads this, Repr
    constructor Init()
      ensures Contents == {}
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
  }
}

abstract module A refines AbstractInterface {
  class StoreAndRetrieve<Thing(==)> ... {
    constructor Init...
    {}
    method Store...
    {}
    method Retrieve...
    {}
  }
}

abstract module B refines A {
  class StoreAndRetrieve<Thing(==)> ... {
    var arr: seq<Thing>
    ghost predicate Valid'...
    {}
    constructor Init...
    {}
    method Store...
    {}
    method Retrieve...
    {}
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {}
  }
}

abstract module AbstractClient {
  import S : AbstractInterface

  method Test() {}
}

module Client refines AbstractClient {
  import S = abC
  method Main() {
    Test();
  }
}

