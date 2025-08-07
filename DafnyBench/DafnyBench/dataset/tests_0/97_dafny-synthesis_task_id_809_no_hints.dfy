method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{}

////////TESTS////////

method TestIsSmaller1() {
    var a := [5, 10, 15];
    var b := [3, 8, 12];
    var result := IsSmaller(a, b);
    assert result == true;
}

method TestIsSmaller2() {
    var a := [5, 10, 15];
    var b := [3, 12, 12];
    var result := IsSmaller(a, b);
    assert result == false;
}

method TestIsSmaller3() {
    var a := [];
    var b := [];
    var result := IsSmaller(a, b);
    assert result == true;
}
