ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{}

lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi')
{}

method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)
    && i + j == i0 + j0
    :: j - i <= hi - lo
{}

method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{}

method {} longestPalindrome'(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{}

function {:opaque} insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
  ensures forall i | 0 <= i <= |s| :: s'[i * 2] == bogus
  ensures forall i | 0 <= i < |s| :: s'[i * 2 + 1] == s[i]
{}

function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
{}

ghost predicate inbound_radius(s': string, c: int, r: int)
{}

ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{}

ghost predicate max_radius(s': string, c: int, r: int)
{}

lemma lemma_palindromic_radius_contains(s': string, c: int, r: int, r': int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires 0 <= r' <= r
  ensures inbound_radius(s', c, r') && palindromic_radius(s', c, r')
{}

lemma lemma_end_of_expansion(s': string, c: int, r: int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires inbound_radius(s', c, r + 1) ==> s'[c - (r + 1)] != s'[c + (r + 1)]
  ensures max_radius(s', c, r)
{}

lemma lemma_mirrored_palindrome(s': string, c: int, r: int, c1: int, r1: int, c2: int)
  requires max_radius(s', c, r) && max_radius(s', c1, r1)
  requires c - r <= c1 < c < c2 <= c + r
  requires c2 - c == c - c1
  ensures c2 + r1 < c + r ==> max_radius(s', c2, r1)
  ensures c2 + r1 > c + r ==> max_radius(s', c2, c + r - c2)
  ensures c2 + r1 == c + r ==> palindromic_radius(s', c2, c + r - c2)
{}

ghost function abs(x: int): int {}

lemma lemma_result_transfer(s: string, s': string, bogus: char, radii: array<int>, c: int, r: int, hi: int, lo: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires radii.Length == |s'|
  requires forall i | 0 <= i < radii.Length :: max_radius(s', i, radii[i])
  requires (c, r) == argmax(radii, 0)
  requires lo == (c - r) / 2 && hi == (c + r) / 2
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{}

ghost predicate max_interval_for_same_center(s: string, k: int, lo: int, hi: int) {}

lemma lemma_palindrome_isomorph(s: string, s': string, bogus: char, lo: int, hi: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= lo <= hi <= |s| 
  ensures palindromic(s, lo, hi) <==> palindromic_radius(s', lo + hi, hi - lo)
{}

lemma lemma_palindrome_bogus(s: string, s': string, bogus: char, c: int, r: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires (c + r) % 2 == 1
  ensures inbound_radius(s', c, r + 1) && palindromic_radius(s', c, r + 1)
{}

////////TESTS////////

method testlongestPalindrome1() {
  var s := "babad";
  var ans, lo, hi := longestPalindrome(s);
  assert ans == "bab" || ans == "aba";
  assert lo == 0 && hi == 3 || lo == 1 && hi == 4 || lo == 2 && hi == 5;
}

method testlongestPalindrome2() {
  var s := "cbbd";
  var ans, lo, hi := longestPalindrome(s);
  assert ans == "bb";
  assert lo == 1 && hi == 3;
}

method testlongestPalindrome3() {
  var s := "a";
  var ans, lo, hi := longestPalindrome(s);
  assert ans == "a";
  assert lo == 0 && hi == 1;
}

method testlongestPalindrome'1() {
  var s := "racecar";
  var ans, lo, hi := longestPalindrome'(s);
  assert ans == "racecar";
  assert lo == 0 && hi == 7;
}

method testlongestPalindrome'2() {
  var s := "ab";
  var ans, lo, hi := longestPalindrome'(s);
  assert ans == "a" || ans == "b";
  assert lo == 0 && hi == 1 || lo == 1 && hi == 2;
}

method testexpand_from_center1() {
  var s := "aba";
  var lo, hi := expand_from_center(s, 1, 1);
  assert lo == 0 && hi == 3;
}

method testexpand_from_center2() {
  var s := "abccba";
  var lo, hi := expand_from_center(s, 2, 3);
  assert lo == 0 && hi == 6;
}

method testinsert_bogus_chars1() {
  var s := "abc";
  var result := insert_bogus_chars(s, '#');
  assert result == "#a#b#c#";
}

method testinsert_bogus_chars2() {
  var s := "";
  var result := insert_bogus_chars(s, '#');
  assert result == "#";
}

method testargmax1() {
  var a := new int[3] [5, 3, 8];
  var result := argmax(a, 0);
  assert result == (2, 8);
}

method testargmax2() {
  var a := new int[4] [1, 7, 3, 7];
  var result := argmax(a, 1);
  assert result == (1, 7) || result == (3, 7);
}

method testabs1() {
  var result := abs(5);
  assert result == 5;
}

method testabs2() {
  var result := abs(-3);
  assert result == 3;
}
