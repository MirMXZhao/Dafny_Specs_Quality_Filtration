ghost function f(x: int, y: int): int

lemma Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)

lemma Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)

lemma DiagonalIdentity(x: int)
  ensures f(x, x) == x

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{}

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  requires A: c <= x
  requires B: x == f(a, b)
  ensures f(a, f(b, c)) <= x
{}

////////TESTS////////

method TestCalculationalStyleProof1() {
  CalculationalStyleProof(2, 3, 1, 5);
}

method TestCalculationalStyleProof2() {
  CalculationalStyleProof(0, 0, -1, 0);
}

method TestDifferentStyleProof1() {
  DifferentStyleProof(2, 3, 1, 5);
}

method TestDifferentStyleProof2() {
  DifferentStyleProof(0, 0, -1, 0);
}
