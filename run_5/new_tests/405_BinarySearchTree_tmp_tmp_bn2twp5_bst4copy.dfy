datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
  decreases tree
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

method GetMin(tree: Tree) returns (res: int)
{}

method GetMax(tree: Tree) returns (res: int){}

method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures BinarySearchTree(res)
{}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
{}

method Inorder(tree: Tree)
{}

method Postorder(tree: Tree)
{}

////////TESTS////////

method TestGetMin1() {
  var tree := Node(Node(Empty, 2, Empty), 5, Node(Empty, 8, Empty));
  var res := GetMin(tree);
  assert res == 2;
}

method TestGetMin2() {
  var tree := Node(Empty, 10, Node(Empty, 15, Empty));
  var res := GetMin(tree);
  assert res == 10;
}

method TestGetMax1() {
  var tree := Node(Node(Empty, 2, Empty), 5, Node(Empty, 8, Empty));
  var res := GetMax(tree);
  assert res == 8;
}

method TestGetMax2() {
  var tree := Node(Node(Empty, 3, Empty), 7, Empty);
  var res := GetMax(tree);
  assert res == 7;
}

method TestInsert1() {
  var tree := Node(Empty, 5, Empty);
  var res := insert(tree, 3);
  assert res == Node(Node(Empty, 3, Empty), 5, Empty);
}

method TestInsert2() {
  var tree := Node(Empty, 5, Empty);
  var res := insert(tree, 7);
  assert res == Node(Empty, 5, Node(Empty, 7, Empty));
}

method TestInsertRecursion1() {
  var tree := Node(Empty, 5, Empty);
  var res := insertRecursion(tree, 3);
  assert res == Node(Node(Empty, 3, Empty), 5, Empty);
}

method TestInsertRecursion2() {
  var tree := Node(Empty, 10, Empty);
  var res := insertRecursion(tree, 15);
  assert res == Node(Empty, 10, Node(Empty, 15, Empty));
}

method TestDelete1() {
  var tree := Node(Node(Empty, 3, Empty), 5, Node(Empty, 7, Empty));
  var res := delete(tree, 3);
  assert res == Node(Empty, 5, Node(Empty, 7, Empty));
}

method TestDelete2() {
  var tree := Node(Empty, 10, Empty);
  var res := delete(tree, 10);
  assert res == Empty;
}

method TestInorder1() {
  var tree := Node(Node(Empty, 2, Empty), 5, Node(Empty, 8, Empty));
  Inorder(tree);
}

method TestInorder2() {
  var tree := Empty;
  Inorder(tree);
}

method TestPostorder1() {
  var tree := Node(Node(Empty, 2, Empty), 5, Node(Empty, 8, Empty));
  Postorder(tree);
}

method TestPostorder2() {
  var tree := Node(Empty, 10, Empty);
  Postorder(tree);
}
