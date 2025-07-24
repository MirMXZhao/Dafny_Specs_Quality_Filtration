method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{}

method TestIsSmaller1() {
    var a := [3, 5, 7];
    var b := [2, 4, 6];
    var result := IsSmaller(a, b);
    assert result == true;
}

method TestIsSmaller2() {
    var a := [3, 2, 7];
    var b := [2, 4, 6];
    var result := IsSmaller(a, b);
    assert result == false;
}
