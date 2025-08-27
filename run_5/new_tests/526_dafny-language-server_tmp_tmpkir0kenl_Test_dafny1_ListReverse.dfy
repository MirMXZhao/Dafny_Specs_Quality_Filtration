class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r;
    requires (forall y :: y in r ==> y.nxt == null || y.nxt in r);
    modifies r;
    ensures reverse == null || reverse in r;
    ensures (forall y :: y in r ==> y.nxt == null || y.nxt in r);
    decreases *;
  {}
}

////////TESTS////////

method TestReverseInPlace1() {
  var node1 := new Node;
  var node2 := new Node;
  var node3 := new Node;
  node1.nxt := node2;
  node2.nxt := node3;
  node3.nxt := null;
  var r := {node1, node2, node3};
  var reverse := node1.ReverseInPlace(node1, r);
  assert reverse == null || reverse in r;
}

method TestReverseInPlace2() {
  var r: set<Node> := {};
  var node := new Node;
  var reverse := node.ReverseInPlace(null, r);
  assert reverse == null || reverse in r;
}
