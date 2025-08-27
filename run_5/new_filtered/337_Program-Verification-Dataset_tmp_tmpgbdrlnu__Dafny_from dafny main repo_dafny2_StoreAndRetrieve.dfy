abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>
    ghost predicate Valid() {
      Valid'()
    }
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
    {
      Contents == set x | x in arr
    }
    constructor Init...
    {}
    method Store...
    {}
    method Retrieve...
    {}
  }
}

module abC refines B {
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {}
  }
}

abstract module AbstractClient {
  import S : AbstractInterface
}

module Client refines AbstractClient {
  import S = abC
}