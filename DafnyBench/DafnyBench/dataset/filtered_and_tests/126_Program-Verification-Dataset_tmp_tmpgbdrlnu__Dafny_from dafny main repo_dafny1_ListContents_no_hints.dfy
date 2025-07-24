// RUN: %testDafnyForEachResolver "%s"


class Node<T> {
  ghost var List: seq<T>
  ghost var Repr: set<Node<T>>

  var data: T
  var next: Node?<T>

  ghost predicate Valid()
    reads this, Repr
  {}

  constructor (d: T)
    ensures Valid() && fresh(Repr)
    ensures List == [d]
  {}

  constructor InitAsPredecessor(d: T, succ: Node<T>)
    requires succ.Valid()
    ensures Valid() && fresh(Repr - succ.Repr)
    ensures List == [d] + succ.List
  {}

  method Prepend(d: T) returns (r: Node<T>)
    requires Valid()
    ensures r.Valid() && fresh(r.Repr - old(Repr))
    ensures r.List == [d] + List
  {}

  method SkipHead() returns (r: Node?<T>)
    requires Valid()
    ensures r == null ==> |List| == 1
    ensures r != null ==> r.Valid() && r.List == List[1..] && r.Repr <= Repr
  {
    r := next;
  }

  method ReverseInPlace() returns (reverse: Node<T>)
    requires Valid()
    modifies Repr
    ensures reverse.Valid() && reverse.Repr <= old(Repr)
    ensures |reverse.List| == |old(List)|
    ensures forall i :: 0 <= i < |reverse.List| ==> reverse.List[i] == old(List)[|old(List)|-1-i]
  {}
}



method TestReverseInPlace1() {
  var node1 := new Node(1);
  var node2 := new Node.InitAsPredecessor(2, node1);
  var node3 := new Node.InitAsPredecessor(3, node2);
  var reverse := node3.ReverseInPlace();
  assert reverse.List == [1, 2, 3];
}

method TestReverseInPlace2() {
  var node := new Node(42);
  var reverse := node.ReverseInPlace();
  assert reverse.List == [42];
}
