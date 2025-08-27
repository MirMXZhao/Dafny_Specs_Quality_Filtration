method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{}

////////TESTS////////

method TestBitwiseXOR1() {
  var a := [0b1010, 0b1100];
  var b := [0b1111, 0b0101];
  var result := BitwiseXOR(a, b);
  assert result == [0b0101, 0b1001];
}

method TestBitwiseXOR2() {
  var a := [0b0000, 0b1111, 0b1010];
  var b := [0b1111, 0b1111, 0b0000];
  var result := BitwiseXOR(a, b);
  assert result == [0b1111, 0b0000, 0b1010];
}
