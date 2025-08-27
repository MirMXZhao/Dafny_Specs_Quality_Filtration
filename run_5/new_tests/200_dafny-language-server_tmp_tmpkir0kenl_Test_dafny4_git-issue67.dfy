class Node { }

predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{}

////////TESTS////////

method TestMainMethod1() {
  var y := new Node;
  MainMethod(y);
}

method TestMainMethod2() {
  var y := new Node;
  MainMethod(y);
}
