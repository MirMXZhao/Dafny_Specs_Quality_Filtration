module DivMod {

  function {:opaque} DivSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {}

  function {:opaque} ModSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {}

  lemma DivModAdd1(a: int, b: int)
    requires b != 0
    ensures (a + b) % b == a % b
    ensures (a + b) / b == a / b + 1
  {}

  lemma DivModSub1(a: int, b: int)
    requires b != 0
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
  {}

  lemma ModEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a % b == ModSub(a, b)
  {}

  lemma DivEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a / b == DivSub(a, b)
  {}

  lemma DivModSpec'(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures ModSub(a, b) == r
    ensures DivSub(a, b) == q
  {}

  lemma DivModSpec(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures a % b == r
    ensures a / b == q
  {}

  lemma DivMul(a: int, b: int)
    requires 0

////////TESTS////////

method TestDivSub1() {
  var a := 10;
  var b := 3;
  var result := DivSub(a, b);
  assert result == 3;
}

method TestDivSub2() {
  var a := 15;
  var b := 5;
  var result := DivSub(a, b);
  assert result == 3;
}

method TestModSub1() {
  var a := 10;
  var b := 3;
  var result := ModSub(a, b);
  assert result == 1;
}

method TestModSub2() {
  var a := 15;
  var b := 5;
  var result := ModSub(a, b);
  assert result == 0;
}
