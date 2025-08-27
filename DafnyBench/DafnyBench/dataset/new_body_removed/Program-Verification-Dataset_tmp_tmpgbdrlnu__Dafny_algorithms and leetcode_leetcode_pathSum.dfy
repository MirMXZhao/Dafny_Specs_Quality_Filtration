//https://leetcode.com/problems/path-sum
/**
function hasPathSum(root: TreeNode | null, targetSum: number): boolean {};
 */

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

method Test() {}



