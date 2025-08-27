method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{}

////////TESTS////////

method TestDeepCopySeq1() {
    var s := [1, 2, 3, 4];
    var copy := DeepCopySeq(s);
    assert copy == [1, 2, 3, 4];
}

method TestDeepCopySeq2() {
    var s := [];
    var copy := DeepCopySeq(s);
    assert copy == [];
}
