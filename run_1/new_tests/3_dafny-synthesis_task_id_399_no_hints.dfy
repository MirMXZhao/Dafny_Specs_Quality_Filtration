method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{}

////////TESTS////////

method TestBitwiseXOR1() {
  var a := [5 as bv32, 3 as bv32, 8 as bv32];
  var b := [3 as bv32, 5 as bv32, 8 as bv32];
  var result := BitwiseXOR(a, b);
  assert result == [6 as bv32, 6 as bv32, 0 as bv32];
}

method TestBitwiseXOR2() {
  var a := [15 as bv32, 0 as bv32];
  var b := [0 as bv32, 15 as bv32];
  var result := BitwiseXOR(a, b);
  assert result == [15 as bv32, 15 as bv32];
}
