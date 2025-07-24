method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{}

method TestCountIdenticalPositions1() {
    var a := [1, 2, 3, 4];
    var b := [1, 5, 3, 7];
    var c := [1, 2, 3, 4];
    var count := CountIdenticalPositions(a, b, c);
    assert count == 2;
}

method TestCountIdenticalPositions2() {
    var a := [10, 20, 30];
    var b := [10, 20, 30];
    var c := [10, 20, 30];
    var count := CountIdenticalPositions(a, b, c);
    assert count == 3;
}
