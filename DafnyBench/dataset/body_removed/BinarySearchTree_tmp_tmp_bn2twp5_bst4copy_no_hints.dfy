datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
{}

predicate maxValue(tree: Tree, max: int)
{}

predicate minValue(tree: Tree, min: int)
{}

method GetMin(tree: Tree) returns (res: int)
{}

method GetMax(tree: Tree) returns (res: int){}

method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  //ensures BinarySearchTree(res)
  //ensures res != Empty ==> BinarySearchTree(res)
{}

method Inorder(tree: Tree)
{}

method Postorder(tree: Tree)
{}

method Main() {}
