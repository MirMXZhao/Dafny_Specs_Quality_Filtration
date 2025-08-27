method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{}

////////TESTS////////

method TestFindSmallest1() {
  var s := new int[4];
  s[0] := 5;
  s[1] := 2;
  s[2] := 8;
  s[3] := 1;
  var min := FindSmallest(s);
  assert min == 1;
}

method TestFindSmallest2() {
  var s := new int[3];
  s[0] := -3;
  s[1] := 7;
  s[2] := -1;
  var min := FindSmallest(s);
  assert min == -3;
}
