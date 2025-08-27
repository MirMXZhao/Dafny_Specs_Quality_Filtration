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