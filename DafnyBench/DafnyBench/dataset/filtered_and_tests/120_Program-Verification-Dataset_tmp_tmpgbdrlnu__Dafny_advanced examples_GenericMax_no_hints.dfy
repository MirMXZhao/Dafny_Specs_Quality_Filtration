method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x);
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);

  ensures forall x :: 0 <= x < a.Length ==>
    // uncommenting the following line causes the program to verify
    // assume cmp.requires(a[x], max);
    cmp(a[x], max)
{}



method TestGenericMax1() {
  var a := new int[3];
  a[0] := 1; a[1] := 5; a[2] := 3;
  var cmp := (x: int, y: int) => x <= y;
  var max := GenericMax(cmp, a);
  assert max == 5;
}

method TestGenericMax2() {
  var a := new int[4];
  a[0] := 10; a[1] := 2; a[2] := 8; a[3] := 6;
  var cmp := (x: int, y: int) => x <= y;
  var max := GenericMax(cmp, a);
  assert max == 10;
}
