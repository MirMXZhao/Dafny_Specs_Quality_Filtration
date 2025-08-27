type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])
}

method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
{}

method lengthOfLongestSubstring'(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
{}

////////TESTS////////

method TestlengthOfLongestSubstring1() {
  var s := "abcabcbb";
  var n, best_iv := lengthOfLongestSubstring(s);
  assert n == 3;
  assert valid_interval(s, best_iv);
  assert length(best_iv) == 3;
}

method TestlengthOfLongestSubstring2() {
  var s := "bbbbb";
  var n, best_iv := lengthOfLongestSubstring(s);
  assert n == 1;
  assert valid_interval(s, best_iv);
  assert length(best_iv) == 1;
}

method TestlengthOfLongestSubstring'1() {
  var s := "pwwkew";
  var n, best_iv := lengthOfLongestSubstring'(s);
  assert n == 3;
  assert valid_interval(s, best_iv);
  assert length(best_iv) == 3;
}

method TestlengthOfLongestSubstring'2() {
  var s := "";
  var n, best_iv := lengthOfLongestSubstring'(s);
  assert n == 0;
  assert valid_interval(s, best_iv);
  assert length(best_iv) == 0;
}
