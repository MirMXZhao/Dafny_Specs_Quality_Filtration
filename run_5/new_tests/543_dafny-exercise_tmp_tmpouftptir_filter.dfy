method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{}

////////TESTS////////

method TestFilter1() {
  var a := ['a', 'b', 'c', 'a'];
  var b := {'a', 'c', 'd'};
  var c := Filter(a, b);
  assert c == {'a', 'c'};
}

method TestFilter2() {
  var a := ['x', 'y', 'z'];
  var b := {'p', 'q', 'r'};
  var c := Filter(a, b);
  assert c == {};
}
