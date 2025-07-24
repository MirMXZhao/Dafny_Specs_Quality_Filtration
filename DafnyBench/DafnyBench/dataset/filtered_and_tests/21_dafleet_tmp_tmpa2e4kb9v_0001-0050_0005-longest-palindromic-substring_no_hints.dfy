/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{}

// A "common sense" about palindromes:
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi')
{}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(s, lo, hi)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo  // `ans` is longest
{}


/* Discussions
1. Dafny is super bad at slicing (esp. nested slicing).
  Do circumvent it whenever possible. It can save you a lot of assertions & lemmas!

  For example, instead of `palindromic(s[i..j])`, use the pattern `palindromic(s, i, j)` instead.
  I didn't realize this (ref: https://github.com/Nangos/dafleet/commit/3302ddd7642240ff2b2f6a8c51e8becd5c9b6437),
  Resulting in a couple of clumsy lemmas.

2. Bonus -- Manacher's algorithm
  Our above solution needs `O(|s|^2)` time in the worst case. Can we improve it? Yes.

  Manacher's algorithm guarantees an `O(|s|)` time.
  To get the intuition, ask yourself: when will it really take `O(|s|^2)` time?
  When there are a lot of "nesting and overlapping" palindromes. like in `abcbcbcba` or even `aaaaaa`.

  Imagine each palindrome as a "mirror". "Large mirrors" reflect "small mirrors".
  Therefore, when we "expand" from some "center", we can "reuse" some information from its "mirrored center".
  For example, we move the "center", from left to right, in the string `aiaOaia...`
  Here, the char `O` is the "large mirror".
  When the current center is the second `i`, it is "mirrored" to the first `i` (which we've calculated for),
  so we know the palindrome centered at the second `i` must have at least a length of 3 (`aia`).
  So we can expand directly from `aia`, instead of expanding from scratch.

  Manacher's algorithm is verified below.
  Also, I will verify that "every loop is entered for only `O(|s|)` times",
  which "indirectly" proves that the entire algorithm runs in `O(|s|)` time.
*/


// A reference implementation of Manacher's algorithm:
// (Ref. https://en.wikipedia.org/wiki/Longest_palindromic_substring#Manacher's_algorithm) for details...
method {} longestPalindrome'(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{}


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
function {:opaque} insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
  ensures forall i | 0 <= i <= |s| :: s'[i * 2] == bogus
  ensures forall i | 0 <= i < |s| :: s'[i * 2 + 1] == s[i]
{}

// Returns (max_index, max_value) of array `a` starting from index `start`.
function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
{}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
ghost predicate inbound_radius(s': string, c: int, r: int)
{}

// Whether `r` is a valid palindromic radius at center `c`.
ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{}

// Whether `r` is the maximal palindromic radius at center `c`.
ghost predicate max_radius(s': string, c: int, r: int)
{}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval
lemma lemma_palindromic_radius_contains(s': string, c: int, r: int, r': int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires 0 <= r' <= r
  ensures inbound_radius(s', c, r') && palindromic_radius(s', c, r')
{}

// When "expand from center" ends, we've find the max radius:
lemma lemma_end_of_expansion(s': string, c: int, r: int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires inbound_radius(s', c, r + 1) ==> s'[c - (r + 1)] != s'[c + (r + 1)]
  ensures max_radius(s', c, r)
{}

// The critical insight behind Manacher's algorithm.
//
// Given the longest palindrome centered at `c` has length `r`, consider the interval from `c-r` to `c+r`.
// Consider a pair of centers in the interval: `c1` (left half) and `c2` (right half), equally away from `c`.
// Then, the length of longest palindromes at `c1` and `c2` are related as follows:
lemma lemma_mirrored_palindrome(s': string, c: int, r: int, c1: int, r1: int, c2: int)
  requires max_radius(s', c, r) && max_radius(s', c1, r1)
  requires c - r <= c1 < c < c2 <= c + r
  requires c2 - c == c - c1
  ensures c2 + r1 < c + r ==> max_radius(s', c2, r1)
  ensures c2 + r1 > c + r ==> max_radius(s', c2, c + r - c2)
  ensures c2 + r1 == c + r ==> palindromic_radius(s', c2, c + r - c2)
{}
//, where:
ghost function abs(x: int): int {}

// Transfering our final result on `s'` to that on `s`:
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

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
ghost predicate max_interval_for_same_center(s: string, k: int, lo: int, hi: int) {}

// Establishes the "palindromic isomorphism" between `s` and `s'`.
lemma lemma_palindrome_isomorph(s: string, s': string, bogus: char, lo: int, hi: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= lo <= hi <= |s| 
  ensures palindromic(s, lo, hi) <==> palindromic_radius(s', lo + hi, hi - lo)
{}

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.
lemma lemma_palindrome_bogus(s: string, s': string, bogus: char, c: int, r: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires (c + r) % 2 == 1
  ensures inbound_radius(s', c, r + 1) && palindromic_radius(s', c, r + 1)
{}



method TestLongestPalindrome1() {
  var s := "babad";
  var ans, lo, hi := longestPalindrome(s);
  assert ans == "bab" || ans == "aba";
  assert lo == 0 && hi == 3 || lo == 1 && hi == 4;
}

method TestLongestPalindrome2() {
  var s := "cbbd";
  var ans, lo, hi := longestPalindrome(s);
  assert ans == "bb";
  assert lo == 1 && hi == 3;
}
