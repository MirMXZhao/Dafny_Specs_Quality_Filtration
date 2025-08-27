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
        decreases stop - start
        {}

        function union_length(s1 : seq<int>, s2 : seq<int>, count : int, i : int, stop : int) : int 
        requires 0 <= i <= stop
        requires stop <= |s1|
        decreases stop - i
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
    var s := new IntegerSet.Set.Set0();
    var size := s.size();
    assert size == 0;
}

method testSet02() {
    var s := new IntegerSet.Set.Set([1, 2, 3]);
    var size := s.size();
    assert size == 3;
}

method testaddElement1() {
    var s := new IntegerSet.Set.Set([1, 2]);
    s.addElement(3);
    assert s.elements == [1, 2, 3] || s.elements == [1, 3, 2] || s.elements == [2, 1, 3] || s.elements == [2, 3, 1] || s.elements == [3, 1, 2] || s.elements == [3, 2, 1];
}

method testaddElement2() {
    var s := new IntegerSet.Set.Set([1, 2]);
    s.addElement(1);
    assert s.elements == [1, 2];
}

method testremoveElement1() {
    var s := new IntegerSet.Set.Set([1, 2, 3]);
    s.removeElement(2);
    assert 2 !in s.elements && 1 in s.elements && 3 in s.elements;
}

method testremoveElement2() {
    var s := new IntegerSet.Set.Set([1, 2]);
    s.removeElement(3);
    assert s.elements == [1, 2];
}

method testcontains1() {
    var s := new IntegerSet.Set.Set([1, 2, 3]);
    var result := s.contains(2);
    assert result == true;
}

method testcontains2() {
    var s := new IntegerSet.Set.Set([1, 2, 3]);
    var result := s.contains(4);
    assert result == false;
}

method testintersect1() {
    var s1 := new IntegerSet.Set.Set([1, 2, 3]);
    var s2 := new IntegerSet.Set.Set([2, 3, 4]);
    var result := s1.intersect(s2);
    assert 2 in result.elements && 3 in result.elements && 1 !in result.elements && 4 !in result.elements;
}

method testintersect2() {
    var s1 := new IntegerSet.Set.Set([1, 2]);
    var s2 := new IntegerSet.Set.Set([3, 4]);
    var result := s1.intersect(s2);
    assert result.elements == [];
}

method testunion1() {
    var s1 := new IntegerSet.Set.Set([1, 2]);
    var s2 := new IntegerSet.Set.Set([3, 4]);
    var result := s1.union(s2);
    assert 1 in result.elements && 2 in result.elements && 3 in result.elements && 4 in result.elements;
}

method testunion2() {
    var s1 := new IntegerSet.Set.Set([1, 2]);
    var s2 := new IntegerSet.Set.Set([2, 3]);
    var result := s1.union(s2);
    assert 1 in result.elements && 2 in result.elements && 3 in result.elements;
}
