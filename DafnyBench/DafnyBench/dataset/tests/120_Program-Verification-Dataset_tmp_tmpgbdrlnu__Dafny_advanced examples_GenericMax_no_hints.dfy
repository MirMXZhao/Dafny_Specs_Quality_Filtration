method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x);
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);

  ensures forall x :: 0 <= x < a.Length ==>
    cmp(a[x], max)
{}

////////TESTS////////

method TestGenericMax1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  var cmp := (x: int, y: int) => x <= y;
  var max := GenericMax(cmp, a);
  assert max == 8;
}

method TestGenericMax2() {
  var a := new int[4];
  a[0] := 10;
  a[1] := 3;
  a[2] := 7;
  a[3] := 1;
  var cmp := (x: int, y: int) => x <= y;
  var max := GenericMax(cmp, a);
  assert max == 10;
}

method TestGenericMax3() {
  var a := new int[1];
  a[0] := 42;
  var cmp := (x: int, y: int) => x <= y;
  var max := GenericMax(cmp, a);
  assert max == 42;
}
