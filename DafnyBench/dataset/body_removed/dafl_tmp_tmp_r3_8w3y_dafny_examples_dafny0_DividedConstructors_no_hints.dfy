// RUN: %dafny /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {}

module M0 {}

module M1 refines M0 {}

module TypeOfThis {
  class LinkedList<T(0)> {
    ghost var Repr: set<LinkedList<T>>
    ghost var Rapr: set<LinkedList?<T>>
    ghost var S: set<object>
    ghost var T: set<object?>

    constructor Init()
    {}

    constructor Init'()
    {}

    constructor Create()
    {}

    constructor Create'()
    {}

    constructor Two()
    {}

    method Mutate()
      modifies this
    {}
  }
}

module Regression {}


