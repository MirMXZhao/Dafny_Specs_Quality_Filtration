// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int


  predicate validDown()
    reads this, desc
  {}




  predicate validUp()
    reads this, anc
  {}

  predicate valid()
    reads this, desc, anc
  {}

  predicate before()
    reads this
  { !sense && pc <= 2 }

  predicate blocked()
    reads this
  { sense }

  predicate after()
    reads this
  { !sense && 3 <= pc }


  method barrier()
    requires valid()
    requires before()
    modifies this, left, right
  {}
}

