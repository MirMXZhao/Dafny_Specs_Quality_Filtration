trait MyMultiset {

  ghost predicate Valid()
    reads this

  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  { elem in theMultiset }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
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

class MultisetImplementationWithMap extends MyMultiset {

  ghost predicate Valid()
    reads this
  {
    (forall i | i in elements.Keys :: elements[i] > 0) && (theMultiset == A(elements)) && (forall i :: i in elements.Keys <==> Contains(i))
  }

  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  var elements: map<int, nat>;

  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {}

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

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {}

  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {}

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {}

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {}

  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {}
}

////////TESTS////////

method TestAdd1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange := ms.Add(5);
  assert didChange == true;
}

method TestAdd2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(3);
  var didChange2 := ms.Add(3);
  assert didChange1 == true;
  assert didChange2 == true;
}

method TestRemove1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(7);
  var didChange2 := ms.Remove(7);
  assert didChange2 == true;
}

method TestRemove2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange := ms.Remove(10);
  assert didChange == false;
}

method TestLength1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(1);
  var didChange2 := ms.Add(2);
  var len := ms.Length();
  assert len == 2;
}

method TestLength2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var len := ms.Length();
  assert len == 0;
}

method TestEquals1() {
  var ms1 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var ms2 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms1.Add(5);
  var didChange2 := ms2.Add(5);
  var equal := ms1.equals(ms2);
  assert equal == true;
}

method TestEquals2() {
  var ms1 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var ms2 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms1.Add(3);
  var didChange2 := ms2.Add(4);
  var equal := ms1.equals(ms2);
  assert equal == false;
}

method TestGetElems1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(2);
  var didChange2 := ms.Add(3);
  var elems := ms.getElems();
  assert multiset(elems) == multiset{2, 3};
}

method TestGetElems2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var elems := ms.getElems();
  assert multiset(elems) == multiset{};
}

method TestMap2Seq1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var m := map[1 := 2, 3 := 1];
  var s := ms.Map2Seq(m);
  assert multiset(s) == multiset{1, 1, 3};
}

method TestMap2Seq2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var m := map[];
  var s := ms.Map2Seq(m);
  assert multiset(s) == multiset{};
}
