function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{}

method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{}

////////TESTS////////

method Testcumsum1() {
  var a := new int[4];
  var b := new int[4];
  a[0] := 2;
  a[1] := 3;
  a[2] := 1;
  a[3] := 4;
  cumsum(a, b);
  assert b[0] == 2;
  assert b[1] == 5;
  assert b[2] == 6;
  assert b[3] == 10;
}

method Testcumsum2() {
  var a := new int[3];
  var b := new int[3];
  a[0] := -1;
  a[1] := 2;
  a[2] := -3;
  cumsum(a, b);
  assert b[0] == -1;
  assert b[1] == 1;
  assert b[2] == -2;
}
