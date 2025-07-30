predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

////////TESTS////////

method TestSharedElements1() {
    var a := new int[3] [1, 2, 3];
    var b := new int[3] [2, 3, 4];
    var result := SharedElements(a, b);
    assert result == [2, 3] || result == [3, 2];
}

method TestSharedElements2() {
    var a := new int[2] [1, 5];
    var b := new int[2] [6, 7];
    var result := SharedElements(a, b);
    assert result == [];
}

method TestSharedElements3() {
    var a := new int[0] [];
    var b := new int[2] [1, 2];
    var result := SharedElements(a, b);
    assert result == [];
}
