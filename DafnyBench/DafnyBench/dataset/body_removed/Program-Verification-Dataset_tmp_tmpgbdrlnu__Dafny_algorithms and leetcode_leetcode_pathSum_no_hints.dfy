//https://leetcode.com/problems/path-sum
/**
function hasPathSum(root: TreeNode | null, targetSum: number): boolean {};
 */

datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)

function TreeSeq(root: TreeNode): seq<TreeNode> {}

function TreeSet(root: TreeNode): set<TreeNode> {}

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {}

function pathSum(paths: seq<TreeNode>): nat {}

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{}

method Test() {}



