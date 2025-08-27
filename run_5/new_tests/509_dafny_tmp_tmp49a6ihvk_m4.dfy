datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}

method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{}

////////TESTS////////

method TestDutchFlag1() {
  var a := new Color[5] [Blue, Red, White, Red, Blue];
  DutchFlag(a);
  assert forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j]);
  assert multiset(a[..]) == multiset([Blue, Red, White, Red, Blue]);
}

method TestDutchFlag2() {
  var a := new Color[3] [White, Blue, Red];
  DutchFlag(a);
  assert forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j]);
  assert multiset(a[..]) == multiset([White, Blue, Red]);
}
