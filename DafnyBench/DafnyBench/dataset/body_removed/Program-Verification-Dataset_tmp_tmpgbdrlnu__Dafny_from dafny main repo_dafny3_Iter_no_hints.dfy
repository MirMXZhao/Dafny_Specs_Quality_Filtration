// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

class List<T> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>

  var a: array<T>
  var n: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {}

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {}

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
  {}
}

class Cell { var data: int }

iterator M<T(0)>(l: List<T>, c: Cell) yields (x: T)
  requires l.Valid()
  reads l.Repr
  modifies c
  yield requires true
  yield ensures xs <= l.Contents  // this is needed in order for the next line to be well-formed
  yield ensures x == l.Contents[|xs|-1]
  ensures xs == l.Contents
{}

method Client<T(==,0)>(l: List, stop: T) returns (s: seq<T>)
  requires l.Valid()
{}

method PrintSequence<T>(s: seq<T>)
{}

method Main()
{}

