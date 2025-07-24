predicate IsVowel(c: char)
{}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{}

method TestCountVowelNeighbors1() {
  var s := "abaca";
  var count := CountVowelNeighbors(s);
  assert count == 1;
}

method TestCountVowelNeighbors2() {
  var s := "hello";
  var count := CountVowelNeighbors(s);
  assert count == 0;
}
