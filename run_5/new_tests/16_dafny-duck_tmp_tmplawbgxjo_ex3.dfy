predicate sortedbad(s: string)
{
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{}

////////TESTS////////

method TestBadSort1() {
  var a := "bad";
  var b := BadSort(a);
  assert b == "bad";
}

method TestBadSort2() {
  var a := "dab";
  var b := BadSort(a);
  assert b == "bad";
}
