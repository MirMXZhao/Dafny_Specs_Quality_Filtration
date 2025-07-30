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

////////TESTS////////

method TestConstructor1() {
  var node := new Node(5);
  assert node.List == [5];
}

method TestConstructor2() {
  var node := new Node("hello");
  assert node.List == ["hello"];
}

method TestInitAsPredecessor1() {
  var node2 := new Node(2);
  var node1 := new Node.InitAsPredecessor(1, node2);
  assert node1.List == [1, 2];
}

method TestInitAsPredecessor2() {
  var node3 := new Node(3);
  var node2 := new Node.InitAsPredecessor(2, node3);
  var node1 := new Node.InitAsPredecessor(1, node2);
  assert node1.List == [1, 2, 3];
}

method TestPrepend1() {
  var node := new Node(2);
  var result := node.Prepend(1);
  assert result.List == [1, 2];
}

method TestPrepend2() {
  var node3 := new Node(3);
  var node2 := new Node.InitAsPredecessor(2, node3);
  var result := node2.Prepend(1);
  assert result.List == [1, 2, 3];
}

method TestSkipHead1() {
  var node2 := new Node(2);
  var node1 := new Node.InitAsPredecessor(1, node2);
  var result := node1.SkipHead();
  assert result != null;
  assert result.List == [2];
}

method TestSkipHead2() {
  var node := new Node(42);
  var result := node.SkipHead();
  assert result == null;
}

method TestReverseInPlace1() {
  var node3 := new Node(3);
  var node2 := new Node.InitAsPredecessor(2, node3);
  var node1 := new Node.InitAsPredecessor(1, node2);
  var reverse := node1.ReverseInPlace();
  assert reverse.List == [3, 2, 1];
}

method TestReverseInPlace2() {
  var node := new Node(42);
  var reverse := node.ReverseInPlace();
  assert reverse.List == [42];
}
