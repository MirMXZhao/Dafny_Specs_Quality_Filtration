method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{}

////////TESTS////////

method TestMinSecondValueFirst1() {
  var s := new seq<int>[3];
  s[0] := [5, 10];
  s[1] := [3, 7];
  s[2] := [8, 7];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 3;
}

method TestMinSecondValueFirst2() {
  var s := new seq<int>[2];
  s[0] := [1, 9, 2];
  s[1] := [4, 6, 8];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 4;
}
