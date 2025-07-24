method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
{}

method TestSmallestMissingNumber1() {
  var s := [0, 1, 2, 4, 5];
  var v := SmallestMissingNumber(s);
  assert v == 3;
}

method TestSmallestMissingNumber2() {
  var s := [1, 2, 3, 4];
  var v := SmallestMissingNumber(s);
  assert v == 0;
}
