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
  s[1] := [3, 8];
  s[2] := [7, 12];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 3;
}

method TestMinSecondValueFirst2() {
  var s := new seq<int>[2];
  s[0] := [1, 5, 9];
  s[1] := [4, 2, 6];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 4;
}

method TestMinSecondValueFirst3() {
  var s := new seq<int>[1];
  s[0] := [10, 20];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 10;
}
