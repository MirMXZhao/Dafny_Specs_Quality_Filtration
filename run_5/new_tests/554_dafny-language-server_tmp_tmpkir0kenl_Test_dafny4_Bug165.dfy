type T
function f(a: T) : bool

method Select(s1: seq<T>) returns (r: seq<T>)
  ensures (forall e: T  :: f(e) ==> multiset(s1)[e] == multiset(r)[e])
  ensures (forall e: T  :: (!f(e)) ==> 0 == multiset(r)[e])

////////TESTS////////

method TestSelect1() {
  var s1 := [];
  var r := Select(s1);
  assert r == [];
}

method TestSelect2() {
  var s1 := [];
  var r := Select(s1);
  assert r == [];
}
