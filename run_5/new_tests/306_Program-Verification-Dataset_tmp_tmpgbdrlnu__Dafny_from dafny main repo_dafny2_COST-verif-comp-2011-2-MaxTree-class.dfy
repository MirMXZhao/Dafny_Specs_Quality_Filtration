class Tree {
  var value: int
  var left: Tree?
  var right: Tree?

  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {}

  function IsEmpty(): bool
    requires Valid();
    reads this, Repr;
    ensures IsEmpty() <==> Contents == [];
  {}

  constructor Empty()
    ensures Valid() && Contents == [];
  {}

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid();
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents;
  {}

  lemma exists_intro<T>(P: T ~> bool, x: T)
    requires P.requires(x)
    requires P(x)
    ensures exists y :: P.requires(y) && P(y)
  {
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty();
    ensures forall x :: x in Contents ==> x <= mx;
    ensures exists x :: x in Contents && x == mx;
    decreases Repr;
  {}
}

////////TESTS////////

method TestComputeMax1() {
  var left := new Tree.Empty();
  var right := new Tree.Empty();
  var tree := new Tree.Node(left, 5, right);
  var mx := tree.ComputeMax();
  assert mx == 5;
}

method TestComputeMax2() {
  var empty1 := new Tree.Empty();
  var empty2 := new Tree.Empty();
  var leftSubtree := new Tree.Node(empty1, 3, empty2);
  var empty3 := new Tree.Empty();
  var empty4 := new Tree.Empty();
  var rightSubtree := new Tree.Node(empty3, 7, empty4);
  var tree := new Tree.Node(leftSubtree, 5, rightSubtree);
  var mx := tree.ComputeMax();
  assert mx == 7;
}
