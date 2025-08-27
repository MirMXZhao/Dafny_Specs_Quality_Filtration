method ToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{}

////////TESTS////////

method TestToCharArray1() {
  var a := ToCharArray("hello");
  assert a.Length == 5;
  assert a[0] == 'h';
  assert a[1] == 'e';
  assert a[2] == 'l';
  assert a[3] == 'l';
  assert a[4] == 'o';
}

method TestToCharArray2() {
  var a := ToCharArray("");
  assert a.Length == 0;
}
