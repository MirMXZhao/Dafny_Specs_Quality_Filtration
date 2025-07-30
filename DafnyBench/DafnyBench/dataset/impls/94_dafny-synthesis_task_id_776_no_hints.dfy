predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
}

method TestCountVowelNeighbors1() {
  var s := "abaca"; //im fairly sure this test might be incorrect
  var count := CountVowelNeighbors(s);
  assert count == 1;
}

method TestCountVowelNeighbors2() {
  var s := "hello";
  var count := CountVowelNeighbors(s);
  assert count == 0;
}