class ExtensibleArray<T(0)> {
  // abstract state
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  //concrete state
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int   // number of elements
  var M: int   // number of elements in depot

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
