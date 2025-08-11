method ToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{}

////////TESTS////////

method TestToCharArray1() {
  var s := "hello";
  var a := ToCharArray(s);
  assert a.Length == 5;
  assert a[0] == 'h' && a[1] == 'e' && a[2] == 'l' && a[3] == 'l' && a[4] == 'o';
}

method TestToCharArray2() {
  var s := "";
  var a := ToCharArray(s);
  assert a.Length == 0;
}
