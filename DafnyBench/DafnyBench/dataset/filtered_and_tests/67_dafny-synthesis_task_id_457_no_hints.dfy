method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{}

method TestMinLengthSublist1() {
    var s := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
    var minSublist := MinLengthSublist(s);
    assert minSublist == [4, 5];
}

method TestMinLengthSublist2() {
    var s := [[1], [2, 3, 4], [5, 6]];
    var minSublist := MinLengthSublist(s);
    assert minSublist == [1];
}
