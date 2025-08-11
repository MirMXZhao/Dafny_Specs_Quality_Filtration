method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{}

////////TESTS////////

method TestCountIdenticalPositions1() {
  var a := [1, 2, 3, 4, 5];
  var b := [1, 3, 3, 5, 5];
  var c := [1, 2, 3, 4, 6];
  var count := CountIdenticalPositions(a, b, c);
  assert count == 2;
}

method TestCountIdenticalPositions2() {
  var a := [7, 8, 9];
  var b := [7, 8, 9];
  var c := [7, 8, 9];
  var count := CountIdenticalPositions(a, b, c);
  assert count == 3;
}
