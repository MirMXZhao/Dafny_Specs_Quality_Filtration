predicate IsVowel(c: char)
{}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{}

////////TESTS////////

method TestCountVowelNeighbors1() {
  var s := "aeiou";
  var count := CountVowelNeighbors(s);
  assert count == 3;
}

method TestCountVowelNeighbors2() {
  var s := "hello";
  var count := CountVowelNeighbors(s);
  assert count == 0;
}

method TestCountVowelNeighbors3() {
  var s := "";
  var count := CountVowelNeighbors(s);
  assert count == 0;
}

method TestCountVowelNeighbors4() {
  var s := "a";
  var count := CountVowelNeighbors(s);
  assert count == 0;
}
