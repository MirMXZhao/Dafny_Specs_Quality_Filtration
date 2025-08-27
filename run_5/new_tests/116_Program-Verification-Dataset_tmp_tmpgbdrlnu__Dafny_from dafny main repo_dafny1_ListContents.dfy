class Node<T> {
  ghost var List: seq<T>
  ghost var Repr: set<Node<T>>

  var data: T
  var next: Node?<T>

  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (next == null ==> List == [data]) &&
    (next != null ==>
        next in Repr && next.Repr <= Repr &&
        this !in next.Repr &&
        List == [data] + next.List &&
        next.Valid())
  }

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

////////TESTS////////

method TestPrepend1() {
  var node := new Node(5);
  var result := node.Prepend(3);
  assert result.List == [3, 5];
}

method TestPrepend2() {
  var node1 := new Node(10);
  var node2 := node1.Prepend(7);
  var result := node2.Prepend(4);
  assert result.List == [4, 7, 10];
}

method TestSkipHead1() {
  var node := new Node(42);
  var result := node.SkipHead();
  assert result == null;
}

method TestSkipHead2() {
  var node1 := new Node(20);
  var node2 := new Node.InitAsPredecessor(15, node1);
  var result := node2.SkipHead();
  assert result != null;
  assert result.List == [20];
}

method TestReverseInPlace1() {
  var node := new Node(8);
  var result := node.ReverseInPlace();
  assert result.List == [8];
}

method TestReverseInPlace2() {
  var node1 := new Node(3);
  var node2 := new Node.InitAsPredecessor(2, node1);
  var node3 := new Node.InitAsPredecessor(1, node2);
  var result := node3.ReverseInPlace();
  assert result.List == [3, 2, 1];
}
