/**
  This ADT represents a multiset.
 */
trait MyMultiset {

  // internal invariant
  ghost predicate Valid()
    reads this

  // abstract variable
  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  {}

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

/**
This implementation implements the ADT with a map.
 */
class MultisetImplementationWithMap extends MyMultiset {

  // valid invariant predicate of the ADT implementation
  ghost predicate Valid()
    reads this
  {}

  // the abstraction function
  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  // lemma for the opposite of the abstraction function
  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  // ADT concrete implementation variable
  var elements: map<int, nat>;

  // constructor of the implementation class that ensures the implementation invariant
  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {}
//adds an element to the multiset
  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures elem in elements ==> elements == elements[elem := elements[elem]]
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures !(elem in elements) ==> elements == elements[elem := 1]
    ensures didChange
    ensures Contains(elem)
    ensures Valid()
  {}

//removes an element from the multiset
  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
   /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {}

//gets the length of the multiset
  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {}

//compares the current multiset with another multiset and determines if they're equal
  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {}

//gets the elements of the multiset as a sequence
  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {}

//Transforms a map to a sequence
  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {}

  method Test1()
    modifies this
  {}

  method Test2()
    modifies this
  {}

  method Test3()
  {}
}
