datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)

function TreeSeq(root: TreeNode): seq<TreeNode> {}

function TreeSet(root: TreeNode): set<TreeNode> {}

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
    if |paths| == 0 then false else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}

function pathSum(paths: seq<TreeNode>): nat {}

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{}

////////TESTS////////

method TestHasPathSum1() {
  var root := Cons(5, Cons(4, Cons(11, Cons(7, Nil, Nil), Cons(2, Nil, Nil)), Nil), Cons(8, Cons(13, Nil, Nil), Cons(4, Nil, Cons(1, Nil, Nil))));
  var b := hasPathSum(root, 22);
  assert b == true;
}

method TestHasPathSum2() {
  var root := Cons(1, Cons(2, Nil, Nil), Cons(3, Nil, Nil));
  var b := hasPathSum(root, 5);
  assert b == false;
}
