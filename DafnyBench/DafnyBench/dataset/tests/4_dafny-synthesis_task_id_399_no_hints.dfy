method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{}

////////TESTS////////

method TestBitwiseXOR1() {
  var a := [5, 3, 9];
  var b := [3, 5, 1];
  var result := BitwiseXOR(a, b);
  assert result == [6, 6, 8];
}

method TestBitwiseXOR2() {
  var a := [15, 0, 7];
  var b := [15, 15, 0];
  var result := BitwiseXOR(a, b);
  assert result == [0, 15, 7];
}
