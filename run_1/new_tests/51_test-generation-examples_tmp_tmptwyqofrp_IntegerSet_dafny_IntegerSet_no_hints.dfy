module IntegerSet {

    class Set {

        var elements: seq<int>;

        constructor Set0() 
        ensures this.elements == []
        ensures |this.elements| == 0
        {}

        constructor Set(elements: seq<int>)
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures this.elements == elements
        ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements|  && j != i:: this.elements[i] != this.elements[j]
        {}

        method size() returns (size : int)
        ensures size == |elements|
        {}

        method addElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> elements == old(elements)
        ensures element !in old(elements) ==> |elements| == |old(elements)| + 1 && element in elements && forall i : int :: i in old(elements) ==> i in elements
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {}

        method removeElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> |elements| == |old(elements)| - 1 && (forall i : int :: i in old(elements) && i != element <==> i in elements) && element !in elements
        ensures element !in old(elements) ==> elements == old(elements)
        ensures forall i, j | 0 <=

////////TESTS////////

method testSet01() {
  var s := new Set0();
  var size := s.size();
  assert size == 0;
}

method testSet02() {
  var s := new Set([1, 3, 5]);
  var size := s.size();
  assert size == 3;
}

method testaddElement1() {
  var s := new Set([1, 3]);
  s.addElement(5);
  assert s.elements == [1, 3, 5] || s.elements == [1, 5, 3] || s.elements == [3, 1, 5] || s.elements == [3, 5, 1] || s.elements == [5, 1, 3] || s.elements == [5, 3, 1];
}

method testaddElement2() {
  var s := new Set([1, 3]);
  s.addElement(1);
  assert s.elements == [1, 3];
}

method testremoveElement1() {
  var s := new Set([1, 3, 5]);
  s.removeElement(3);
  assert s.elements == [1, 5] || s.elements == [5, 1];
}

method testremoveElement2() {
  var s := new Set([1, 3, 5]);
  s.removeElement(7);
  assert s.elements == [1, 3, 5];
}
