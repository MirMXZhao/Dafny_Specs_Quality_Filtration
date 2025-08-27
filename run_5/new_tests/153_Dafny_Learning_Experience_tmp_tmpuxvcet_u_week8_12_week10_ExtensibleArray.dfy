class ExtensibleArray<T(0)> {
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int
  var M: int

  ghost predicate Valid()
    decreases Repr +{this}
    reads this, Repr
    ensures Valid() ==> this in Repr
  {}

  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {}

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    ensures Get(i) == Elements[i]
    reads Repr
  {}

  method Set(i: int, t: T)
    requires Valid() && 0 <= i < |Elements|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements)[i := t]
{}

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
    decreases |Elements|
  {}
  
}

////////TESTS////////

method TestGet1() {
  var arr := new ExtensibleArray<int>();
  arr.Add(5);
  arr.Add(10);
  arr.Add(15);
  var result := arr.Get(1);
  assert result == 10;
}

method TestGet2() {
  var arr := new ExtensibleArray<int>();
  arr.Add(42);
  var result := arr.Get(0);
  assert result == 42;
}
