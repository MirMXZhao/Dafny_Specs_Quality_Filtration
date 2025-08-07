function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{}


function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{}


method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{}

////////TESTS////////

method TestMinPair1() {
  var s := [3, 1];
  var r := MinPair(s);
  assert r == 1;
}

method TestMinPair2() {
  var s := [2, 5];
  var r := MinPair(s);
  assert r == 2;
}

method TestMinPair3() {
  var s := [4, 4];
  var r := MinPair(s);
  assert r == 4;
}

method Testmin1() {
  var s := [5, 2, 8, 1];
  var r := min(s);
  assert r == 1;
}

method Testmin2() {
  var s := [10, 3, 7];
  var r := min(s);
  assert r == 3;
}

method Testmin3() {
  var s := [6, 6];
  var r := min(s);
  assert r == 6;
}

method TestSecondSmallest1() {
  var s := new int[4];
  s[0] := 3;
  s[1] := 1;
  s[2] := 4;
  s[3] := 2;
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 2;
}

method TestSecondSmallest2() {
  var s := new int[3];
  s[0] := 7;
  s[1] := 2;
  s[2] := 9;
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 7;
}

method TestSecondSmallest3() {
  var s := new int[5];
  s[0] := 1;
  s[1] := 1;
  s[2] := 3;
  s[3] := 2;
  s[4] := 5;
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 2;
}
