class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int


  predicate validDown()
    reads this, desc
  {
    this !in desc &&
    left != right &&

    (right != null ==> right in desc && left !in right.desc) &&

    (left != null ==>
      left in desc &&
      (right != null ==> desc == {left,right} + left.desc + right.desc)  &&
      (right == null ==> desc == {left} + left.desc)  &&
      left.validDown()) &&
    (left == null ==>
      (right != null ==> desc == {right} + right.desc)  &&
      (right == null ==> desc == {})) &&

    (right != null ==> right.validDown()) &&

    (blocked() ==> forall m :: m in desc ==> m.blocked()) &&
    (after() ==> forall m :: m in desc ==> m.blocked() || m.after())
  }




  predicate validUp()
    reads this, anc
  {
    this !in anc &&
    (parent != null ==> parent in anc && anc == { parent } + parent.anc && parent.validUp()) &&
    (parent == null ==> anc == {}) &&
    (after() ==> forall m :: m in anc ==> m.after())
  }

  predicate valid()
    reads this, desc, anc
  { validUp() && validDown() && desc !! anc }

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }


  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
    decreases *
  {}
}

////////TESTS////////

method TestBarrier1() {
  var node := new Node;
  node.left := null;
  node.right := null;
  node.parent := null;
  node.anc := {};
  node.desc := {};
  node.sense := false;
  node.pc := 1;
  node.barrier();
}

method TestBarrier2() {
  var node := new Node;
  var leftChild := new Node;
  node.left := leftChild;
  node.right := null;
  node.parent := null;
  node.anc := {};
  node.desc := {leftChild};
  node.sense := false;
  node.pc := 2;
  leftChild.left := null;
  leftChild.right := null;
  leftChild.parent := node;
  leftChild.anc := {node};
  leftChild.desc := {};
  leftChild.sense := false;
  leftChild.pc := 1;
  node.barrier();
}
