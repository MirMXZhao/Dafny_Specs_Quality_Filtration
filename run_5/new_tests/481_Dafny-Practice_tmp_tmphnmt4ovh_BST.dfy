datatype Tree = Empty | Node(int,Tree,Tree)

method PrintTreeNumbersInorder(t: Tree)
{}

function NumbersInTree(t: Tree): set<int>
{}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{}

method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{}

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}

lemma {:verify true} lemma_all_small(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k < i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] < i
{}

lemma {:verify true} lemma_all_big(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k > i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] > i
{}

////////TESTS////////

method TestBuildBST1() {
  var q := [5, 3, 7];
  var t := BuildBST(q);
  assert BST(t);
  assert NumbersInTree(t) == {5, 3, 7};
}

method TestBuildBST2() {
  var q := [1, 2, 4, 6];
  var t := BuildBST(q);
  assert BST(t);
  assert NumbersInTree(t) == {1, 2, 4, 6};
}

method TestInsertBST1() {
  var t0 := Node(5, Node(3, Empty, Empty), Node(7, Empty, Empty));
  var t := InsertBST(t0, 4);
  assert BST(t);
  assert NumbersInTree(t) == {3, 4, 5, 7};
}

method TestInsertBST2() {
  var t0 := Node(10, Empty, Empty);
  var t := InsertBST(t0, 15);
  assert BST(t);
  assert NumbersInTree(t) == {10, 15};
}
