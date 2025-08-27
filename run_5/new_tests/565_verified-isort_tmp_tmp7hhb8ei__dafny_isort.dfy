predicate sorted(a: seq<nat>)
{
    true // TODO
}

method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{}

////////TESTS////////

method TestIsort1() {
  var a := new nat[4] := [3, 1, 4, 2];
  Isort(a);
  assert sorted(a[..]);
}

method TestIsort2() {
  var a := new nat[3] := [5, 2, 8];
  Isort(a);
  assert sorted(a[..]);
}
