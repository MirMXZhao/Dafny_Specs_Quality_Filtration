method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0;
requires |s| > 0 ==> i < |s| && j < |s|;
ensures multiset(s[..]) == multiset(t[..]);
ensures |s| == |t|;
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
ensures |s| == 0 ==> t == s;
{}

////////TESTS////////

method TestStringSwap1() {
  var s := "hello";
  var t := StringSwap(s, 1, 3);
  assert t == "hllo";
}

method TestStringSwap2() {
  var s := "";
  var t := StringSwap(s, 0, 0);
  assert t == "";
}

method TestStringSwap3() {
  var s := "abc";
  var t := StringSwap(s, 0, 2);
  assert t == "cba";
}

method TestStringSwap4() {
  var s := "x";
  var t := StringSwap(s, 0, 0);
  assert t == "x";
}
