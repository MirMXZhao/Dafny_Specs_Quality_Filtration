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
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{}


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

method TestMin1() {
  var s := [5, 2, 8, 1];
  var r := min(s);
  assert r == 1;
}

method TestMin2() {
  var s := [3, 7];
  var r := min(s);
  assert r == 3;
}

method TestSecondSmallest1() {
  var s := new int[4];
  s[0] := 1;
  s[1] := 3;
  s[2] := 2;
  s[3] := 4;
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 2;
}

method TestSecondSmallest2() {
  var s := new int[3];
  s[0] := 5;
  s[1] := 1;
  s[2] := 3;
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 3;
}
