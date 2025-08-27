datatype Dt =
  | A(x: int, y: real)
  | B(h: MyClass, x: int)
  | C(y: real)

class MyClass { }

datatype Klef =
  | C0(0: int, 1: int, 2: int, c0: int)
  | C1(1: int, 2: int, 3: int, c1: int)
  | C2(2: int, 3: int, 0: int, c2: int)
  | C3(3: int, 0: int, 1: int, c3: int)

method BaseKlef(k: Klef)
  requires !k.C0? && !k.C2? && !k.C1?
{}

datatype Datte<T> = AA(a: int, x: int) | BB(b: bool, x: int) | CC(c: real) | DD(x: int, o: set<int>, p: bv27, q: T)

method Matte(d: Datte<real>)
  requires !d.CC?
{}

////////TESTS////////

method TestBaseKlef1() {
  var k := C3(5, 10, 15, 20);
  BaseKlef(k);
}

method TestBaseKlef2() {
  var k := C3(0, 0, 0, 0);
  BaseKlef(k);
}

method TestMatte1() {
  var d := AA(5, 10);
  Matte(d);
}

method TestMatte2() {
  var d := DD(3, {1, 2, 3}, 100, 3.14);
  Matte(d);
}
