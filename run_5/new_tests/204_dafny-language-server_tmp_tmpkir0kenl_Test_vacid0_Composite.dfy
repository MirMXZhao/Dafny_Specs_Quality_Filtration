class Composite {
  var left: Composite?
  var right: Composite?
  var parent: Composite?
  var val: int
  var sum: int

  function Valid(S: set<Composite>): bool
    reads this, parent, left, right
  {}

  function Acyclic(S: set<Composite>): bool
    reads S
  {}

  method Init(x: int)
    modifies this
    ensures Valid({this}) && Acyclic({this}) && val == x && parent == null
  {}

  method Update(x: int, ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent)
    ensures forall c :: c in S && c != this ==> c.val == old(c.val)
    ensures val == x
  {}

  method Add(ghost S: set<Composite>, child: Composite, ghost U: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    requires child in U
    requires forall c :: c in U ==> c.Valid(U)
    requires S !! U
    requires left == null || right == null
    requires child.parent == null
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c :: c in S && c != this ==> c.left == old(c.left) && c.right == old(c.right)
    ensures old(left) != null ==> left == old(left)
    ensures old(right) != null ==> right == old(right)
    ensures forall c :: c in S ==> c.parent == old(c.parent) && c.val == old(c.val)
    ensures child.parent == this
    ensures forall c: Composite {:autotriggers false} :: c in S+U ==> c.Valid(S+U)
  {}

  method Dislodge(ghost S: set<Composite>)
    requires this in S && Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.val == old(c.val)
    ensures forall c :: c in S && c != this ==> c.parent == old(c.parent)
    ensures parent == null
    ensures forall c :: c in S ==> c.left == old(c.left) || (old(c.left) == this && c.left == null)
    ensures forall c :: c in S ==> c.right == old(c.right) || (old(c.right) == this && c.right == null)
    ensures Acyclic({this})
  {}

  method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && Acyclic(U)
    requires forall c :: c in S && c != this ==> c.Valid(S)
    requires parent != null ==> parent in S && (parent.left == this || parent.right == this)
    requires left != null ==> left in S && left.parent == this && left != right
    requires right != null ==> right in S && right.parent == this && left != right
    requires sum + delta == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
    modifies U`sum
    ensures forall c :: c in S ==> c.Valid(S)
  {}
}

////////TESTS////////

method TestInit1() {
  var c := new Composite;
  c.Init(42);
  assert c.val == 42;
  assert c.parent == null;
}

method TestInit2() {
  var c := new Composite;
  c.Init(-10);
  assert c.val == -10;
  assert c.parent == null;
}

method TestUpdate1() {
  var c := new Composite;
  c.Init(5);
  var S := {c};
  c.Update(15, S);
  assert c.val == 15;
}

method TestUpdate2() {
  var c := new Composite;
  c.Init(0);
  var S := {c};
  c.Update(-7, S);
  assert c.val == -7;
}

method TestAdd1() {
  var parent := new Composite;
  var child := new Composite;
  parent.Init(10);
  child.Init(5);
  var S := {parent};
  var U := {child};
  parent.Add(S, child, U);
  assert child.parent == parent;
}

method TestAdd2() {
  var parent := new Composite;
  var child := new Composite;
  parent.Init(20);
  child.Init(15);
  var S := {parent};
  var U := {child};
  parent.Add(S, child, U);
  assert child.parent == parent;
}

method TestDislodge1() {
  var c := new Composite;
  c.Init(8);
  var S := {c};
  c.Dislodge(S);
  assert c.parent == null;
}

method TestDislodge2() {
  var c := new Composite;
  c.Init(25);
  var S := {c};
  c.Dislodge(S);
  assert c.parent == null;
}

method TestAdjust1() {
  var c := new Composite;
  c.Init(10);
  c.sum := 10;
  var U := {c};
  var S := {c};
  c.Adjust(0, U, S);
}

method TestAdjust2() {
  var c := new Composite;
  c.Init(5);
  c.sum := 8;
  var U := {c};
  var S := {c};
  c.Adjust(3, U, S);
}
