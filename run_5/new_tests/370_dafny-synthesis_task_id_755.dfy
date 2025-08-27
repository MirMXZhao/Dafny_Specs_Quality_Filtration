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

method TestSecondSmallest1() {
  var s := new int[4] [1, 3, 2, 1];
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 2;
}

method TestSecondSmallest2() {
  var s := new int[3] [5, 2, 8];
  var secondSmallest := SecondSmallest(s);
  assert secondSmallest == 5;
}
