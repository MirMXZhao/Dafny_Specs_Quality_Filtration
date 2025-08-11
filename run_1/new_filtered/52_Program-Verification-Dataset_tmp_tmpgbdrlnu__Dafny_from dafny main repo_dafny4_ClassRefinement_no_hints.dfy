abstract module M0 {
  class Counter {
    ghost var N: int
    ghost var Repr: set<object>
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    constructor Init()
      ensures N == 0
      ensures Valid() && fresh(Repr)
    {}

    method Inc()
      requires Valid()
      modifies Repr
      ensures N == old(N) + 1
      ensures Valid() && fresh(Repr - old(Repr))
    {}

    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {}
  }
}

module M1 refines M0 {
  class Cell {}

  class Counter ... {
    var c: Cell
    var d: Cell
    ghost predicate Valid...
    {}

    constructor Init...
    {}

    method Inc...
    {}

    method Get...
    {}
  }
}