// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
    // modifies only one of this.left and this.right, and child.parent, and various sum fields:
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c :: c in S && c != this ==> c.left == old(c.left) && c.right == old(c.right)
    ensures old(left) != null ==> left == old(left)
    ensures old(right) != null ==> right == old(right)
    ensures forall c :: c in S ==> c.parent == old(c.parent) && c.val == old(c.val)
    // sets child.parent to this:
    ensures child.parent == this
    // leaves everything in S+U valid
    ensures forall c: Composite {:autotriggers false} :: c in S+U ==> c.Valid(S+U) // We can't generate a trigger for this at the moment; if we did, we would still need to prevent TrSplitExpr from translating c in S+U to S[c] || U[c].
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

  /*private*/ method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && Acyclic(U)
    // everything else is valid:
    requires forall c :: c in S && c != this ==> c.Valid(S)
    // this is almost valid:
    requires parent != null ==> parent in S && (parent.left == this || parent.right == this)
    requires left != null ==> left in S && left.parent == this && left != right
    requires right != null ==> right in S && right.parent == this && left != right
    // ... except that sum needs to be adjusted by delta:
    requires sum + delta == val + (if left == null then 0 else left.sum) + (if right == null then 0 else right.sum)
    // modifies sum fields in U:
    modifies U`sum
    // everything is valid, including this:
    ensures forall c :: c in S ==> c.Valid(S)
  {}
}

method Main()
{}

method Harness() {}


