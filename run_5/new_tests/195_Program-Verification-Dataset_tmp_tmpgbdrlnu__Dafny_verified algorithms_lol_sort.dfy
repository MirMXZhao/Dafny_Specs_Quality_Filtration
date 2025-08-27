predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{}

predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}

method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
{}

////////TESTS////////

method TestLolSort1() {
  var a := new int[4];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 2;
  var old_a := a[..];
  lol_sort(a);
  assert valid_permut(a[..], old_a);
  assert sorted(a[..]);
}

method TestLolSort2() {
  var a := new int[3];
  a[0] := 5; a[1] := 5; a[2] := 5;
  var old_a := a[..];
  lol_sort(a);
  assert valid_permut(a[..], old_a);
  assert sorted(a[..]);
}
