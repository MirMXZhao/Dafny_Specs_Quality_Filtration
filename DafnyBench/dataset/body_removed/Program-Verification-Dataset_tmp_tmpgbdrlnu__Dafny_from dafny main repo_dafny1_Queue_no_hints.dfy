// RUN: %testDafnyForEachResolver "%s"


// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

class Queue<T(0)> {
  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var footprint: set<object>
  ghost var spine: set<Node<T>>

  ghost predicate Valid()
    reads this, footprint
  {}

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures |contents| == 0
  {}

  method Rotate()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..] + old(contents)[..1]
  {}

  method RotateAny()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures |contents| == |old(contents)|
    ensures exists i :: 0 <= i && i <= |contents| &&
              contents == old(contents)[i..] + old(contents)[..i]
  {}

  method IsEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty <==> |contents| == 0
  {}

  method Enqueue(t: T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents) + [t]
  {}

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {}

  method Dequeue()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..]
  {}
}

class Node<T(0)> {}

class Main<U(0)> {
  method A<T(0)>(t: T, u: T, v: T)
  {}

  method Main2(t: U, u: U, v: U, q0: Queue<U>, q1: Queue<U>)
    requires q0.Valid()
    requires q1.Valid()
    requires q0.footprint !! q1.footprint
    requires |q0.contents| == 0
    modifies q0.footprint, q1.footprint
    ensures fresh(q0.footprint - old(q0.footprint))
    ensures fresh(q1.footprint - old(q1.footprint))
  {}
}

