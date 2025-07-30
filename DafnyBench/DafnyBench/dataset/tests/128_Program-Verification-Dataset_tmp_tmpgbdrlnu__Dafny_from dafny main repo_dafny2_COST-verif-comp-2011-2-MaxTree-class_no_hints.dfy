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
  var left := new Tree.Empty();
  var rightLeft := new Tree.Empty();
  var rightRight := new Tree.Empty();
  var right := new Tree.Node(rightLeft, 10, rightRight);
  var tree := new Tree.Node(left, 3, right);
  var mx := tree.ComputeMax();
  assert mx == 10;
}

method TestComputeMax3() {
  var leftLeft := new Tree.Empty();
  var leftRight := new Tree.Empty();
  var left := new Tree.Node(leftLeft, 15, leftRight);
  var right := new Tree.Empty();
  var tree := new Tree.Node(left, 8, right);
  var mx := tree.ComputeMax();
  assert mx == 15;
}
