class ExtensibleArray<T(0)> {
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int
  var M: int

  ghost predicate Valid()
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
  {}
  
}

////////TESTS////////

method TestExtensibleArrayGet1() {
  var arr := new ExtensibleArray<int>();
  arr.Add(10);
  arr.Add(20);
  arr.Add(30);
  var result := arr.Get(1);
  assert result == 20;
}

method TestExtensibleArrayGet2() {
  var arr := new ExtensibleArray<int>();
  arr.Add(5);
  var result := arr.Get(0);
  assert result == 5;
}

method TestExtensibleArraySet1() {
  var arr := new ExtensibleArray<int>();
  arr.Add(10);
  arr.Add(20);
  arr.Set(0, 15);
}

method TestExtensibleArraySet2() {
  var arr := new ExtensibleArray<int>();
  arr.Add(100);
  arr.Add(200);
  arr.Add(300);
  arr.Set(2, 350);
}

method TestExtensibleArrayAdd1() {
  var arr := new ExtensibleArray<int>();
  arr.Add(42);
}

method TestExtensibleArrayAdd2() {
  var arr := new ExtensibleArray<int>();
  arr.Add(1);
  arr.Add(2);
  arr.Add(3);
}
