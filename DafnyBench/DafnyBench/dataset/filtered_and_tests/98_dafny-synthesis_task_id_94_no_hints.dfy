method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{}

method TestMinSecondValueFirst1() {
  var s := new seq<int>[3];
  s[0] := [5, 3];
  s[1] := [7, 1];
  s[2] := [2, 4];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 7;
}

method TestMinSecondValueFirst2() {
  var s := new seq<int>[2];
  s[0] := [10, 8, 6];
  s[1] := [15, 2, 9];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 15;
}
