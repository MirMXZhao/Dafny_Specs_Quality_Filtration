module DafnyVersion {
  datatype Pair = Pair(x: int, y: int)

  function pair_x(p: Pair): int {
    p.x
  }

  function pair_y(p: Pair): int {
    p.y
  }
}

module Encoding {

  type Pair(==)

  function pair(x: int, y: int): Pair
  function pair_x(p: Pair): int
  function pair_y(p: Pair): int

  lemma {:axiom} x_defn()
    ensures forall x, y :: pair_x(pair(x, y)) == x
  lemma {:axiom} y_defn()
    ensures forall x, y :: pair_y(pair(x, y)) == y
  lemma {:axiom} bijection()
    ensures forall p:Pair :: pair(pair_x(p), pair_y(p)) == p
}

////////TESTS////////

method TestEncodeDecodeShift1() {
  var operations := [1, -2, 3, -4];
  var encoded := encode_decode_shift(operations, 2);
  assert encoded == [-1, 4, -5, 6];
}

method TestEncodeDecodeShift2() {
  var operations := [5, 10, -3];
  var encoded := encode_decode_shift(operations, 1);
  assert encoded == [-6, -11, 4];
}
