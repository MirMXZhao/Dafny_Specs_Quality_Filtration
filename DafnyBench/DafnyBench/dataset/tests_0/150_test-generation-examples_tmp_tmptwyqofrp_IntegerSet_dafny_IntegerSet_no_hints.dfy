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
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {}

        method contains(element : int) returns (contains : bool)
        ensures contains == (element in elements)
        ensures elements == old(elements)
        {}

        function intersect_length(s1 : seq<int>, s2 : seq<int>, count : int, start : int, stop : int) : int 
        requires 0 <= start <= stop
        requires stop <= |s1|
        {}

        function union_length(s1 : seq<int>, s2 : seq<int>, count : int, i : int, stop : int) : int 
        requires 0 <= i <= stop
        requires stop <= |s1|
        {}

        method intersect(s : Set) returns (intersection : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in intersection.elements <==> i in s.elements && i in this.elements 
        ensures forall i : int :: i !in intersection.elements  <==> i !in s.elements || i !in this.elements
        ensures forall j, k | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k]
        ensures fresh(intersection)
        {}

        method union(s : Set) returns (union : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in s.elements || i in this.elements <==> i in union.elements
        ensures forall i : int :: i !in s.elements && i !in this.elements <==> i !in union.elements
        ensures forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
        ensures fresh(union)
        {}
    }
}

////////TESTS////////

method testSet01() {
    var s := new Set.Set0();
    var size := s.size();
    assert size == 0;
}

method testSet02() {
    var s := new Set.Set([1, 2, 3]);
    var size := s.size();
    assert size == 3;
}

method testSet03() {
    var s := new Set.Set([]);
    var size := s.size();
    assert size == 0;
}

method testaddElement1() {
    var s := new Set.Set([1, 2, 3]);
    s.addElement(4);
    assert 4 in s.elements;
}

method testaddElement2() {
    var s := new Set.Set([1, 2, 3]);
    s.addElement(2);
    assert s.elements == [1, 2, 3];
}

method testaddElement3() {
    var s := new Set.Set([]);
    s.addElement(1);
    assert 1 in s.elements;
    assert |s.elements| == 1;
}

method testremoveElement1() {
    var s := new Set.Set([1, 2, 3]);
    s.removeElement(2);
    assert 2 !in s.elements;
}

method testremoveElement2() {
    var s := new Set.Set([1, 2, 3]);
    s.removeElement(4);
    assert s.elements == [1, 2, 3];
}

method testremoveElement3() {
    var s := new Set.Set([5]);
    s.removeElement(5);
    assert 5 !in s.elements;
    assert |s.elements| == 0;
}

method testcontains1() {
    var s := new Set.Set([1, 2, 3]);
    var contains := s.contains(2);
    assert contains == true;
}

method testcontains2() {
    var s := new Set.Set([1, 2, 3]);
    var contains := s.contains(4);
    assert contains == false;
}

method testcontains3() {
    var s := new Set.Set([]);
    var contains := s.contains(1);
    assert contains == false;
}

method testintersect1() {
    var s1 := new Set.Set([1, 2, 3]);
    var s2 := new Set.Set([2, 3, 4]);
    var intersection := s1.intersect(s2);
    assert 2 in intersection.elements;
    assert 3 in intersection.elements;
    assert 1 !in intersection.elements;
    assert 4 !in intersection.elements;
}

method testintersect2() {
    var s1 := new Set.Set([1, 2]);
    var s2 := new Set.Set([3, 4]);
    var intersection := s1.intersect(s2);
    assert intersection.elements == [];
}

method testintersect3() {
    var s1 := new Set.Set([]);
    var s2 := new Set.Set([1, 2]);
    var intersection := s1.intersect(s2);
    assert intersection.elements == [];
}

method testunion1() {
    var s1 := new Set.Set([1, 2]);
    var s2 := new Set.Set([2, 3]);
    var union := s1.union(s2);
    assert 1 in union.elements;
    assert 2 in union.elements;
    assert 3 in union.elements;
}

method testunion2() {
    var s1 := new Set.Set([1]);
    var s2 := new Set.Set([2]);
    var union := s1.union(s2);
    assert 1 in union.elements;
    assert 2 in union.elements;
}

method testunion3() {
    var s1 := new Set.Set([]);
    var s2 := new Set.Set([]);
    var union := s1.union(s2);
    assert union.elements == [];
}
