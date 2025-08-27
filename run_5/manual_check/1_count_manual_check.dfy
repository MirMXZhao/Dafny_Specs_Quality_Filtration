// Kept File 1:
// filename: dafny-workout_tmp_tmp0abkw6f8_starter_ex02.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-workout_tmp_tmp0abkw6f8_starter_ex02.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 12
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 1
// keepToss: KEEP

method Abs(x: int) returns (y: int)
	requires x < 0
	ensures 0 < y
	ensures y == -x
{
	return -x;
}

method Main()
{}


// Kept File 2:
// filename: dafny-synthesis_task_id_624.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_624.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 2
// num_ensures: 2
// num_requires: 0
// num_lines: 18
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{}

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{}

// Kept File 3:
// filename: Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 11
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}


// Kept File 4:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TuringFactorial.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TuringFactorial.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 1
// num_requires: 1
// num_lines: 12
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 1
// keepToss: KEEP

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{}


// Kept File 5:
// filename: dafny-synthesis_task_id_808.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_808.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 0
// num_lines: 3
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{}
// Kept File 6:
// filename: dafny_examples_tmp_tmp8qotd4ez_leetcode_0069-sqrt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny_examples_tmp_tmp8qotd4ez_leetcode_0069-sqrt.dfy
// num_methods: 1
// num_lemmas: 1
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 2
// num_requires: 2
// num_lines: 16
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{}

// Kept File 7:
// filename: DafnyProjects_tmp_tmp2acw_s4s_CombNK.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/DafnyProjects_tmp_tmp2acw_s4s_CombNK.dfy
// num_methods: 3
// num_lemmas: 1
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 1
// num_requires: 2
// num_lines: 28
// num_no_ensures: 1
// num_no_requires: 0
// num_none_either: 3
// keepToss: KEEP


/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{}
by method
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
{}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

method Main()
{}

method testComb() {}




// Kept File 8:
// filename: dafny-synthesis_task_id_790.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_790.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 1
// num_requires: 0
// num_lines: 8
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{}
// Kept File 9:
// filename: Correctness_tmp_tmpwqvg5q_4_MethodCalls_q1.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Correctness_tmp_tmpwqvg5q_4_MethodCalls_q1.dfy
// num_methods: 1
// num_lemmas: 4
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 5
// num_requires: 1
// num_lines: 30
// num_no_ensures: 0
// num_no_requires: 4
// num_none_either: 1
// keepToss: KEEP

/**
  (a) Verify whether or not the following program
      satisfies total correctness.
      You should use weakest precondition reasoning
      and may extend the loop invariant if required.
      You will need to add a decreases clause to prove termination
  (a) Weakest precondition proof (without termination) (6 marks)
      Termination proof (2marks)
*/

function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)


method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{}

// Kept File 10:
// filename: Clover_is_even.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_is_even.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 0
// num_lines: 4
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
{}

// Kept File 11:
// filename: Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week8_CheckSumCalculator.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week8_CheckSumCalculator.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 1
// num_functions: 4
// num_predicates: 1
// num_ensures: 4
// num_requires: 3
// num_lines: 42
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 2
// keepToss: KEEP

ghost function Hash(s:string):int {}

ghost function SumChars(s: string):int {}
class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {
        cs == Hash(data)
    }

    constructor ()
        ensures Valid() && data == ""
    {}

    method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
    {}

    function GetData(): string
        requires Valid()
        reads this
        ensures Hash(GetData()) == Checksum()
    {
        data
    }

    function Checksum(): int 
        requires Valid()
        reads this 
        ensures Checksum() == Hash(data)
    {
        cs
    }
}

method Main() {}

// Kept File 12:
// filename: dafny-synthesis_task_id_310.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_310.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 0
// num_lines: 4
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method ToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{}
// Kept File 13:
// filename: dafleet_tmp_tmpa2e4kb9v_0001-0050_0003-longest-substring-without-repeating-characters.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafleet_tmp_tmpa2e4kb9v_0001-0050_0003-longest-substring-without-repeating-characters.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 1
// num_ensures: 4
// num_requires: 0
// num_lines: 80
// num_no_ensures: 0
// num_no_requires: 2
// num_none_either: 1
// keepToss: KEEP

/* https://leetcode.com/problems/longest-substring-without-repeating-characters/
Given a string s, find the length of the longest substring without repeating characters.

Example 1:
Input: s = "abcabcbb"
Output: 3
Explanation: The answer is "abc", with the length of 3.
*/


// a left-inclusive right-exclusive interval:
type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)                             // interval is in valid range
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])   // no repeating characters in interval
}

// Below shows an efficient solution using standard "sliding window" technique. 
// For verification simplicity, we pretend as if:
// - `set` were Python set (or even better, a fixed-size array -- if the "alphabet" is small)
//
// `best_iv` is for verification purpose, not returned by the real program, thus `ghost`.
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
{}


/* Discussions
1. The "sliding window" technique is the most "fancy" part of the solution,
  ensuring an O(n) time despite the O(n^2) search space.
  The reason why it works lies in the last two invariants: (A) and (B).

  Invariant (A) is simply a "partial" guarantee for the longest valid substring in `s[..hi]`,
  so once the loop finishes, as `hi == |s|`, this "partial" guarantee becomes "full".

  Invariant (B) is crucial: it encodes why we can monotonically increase `lo` as we increase `hi`.
  What's the "intuition" behind that? Let me share an "informal proof" below:
  
    Let `sub(i)` be the longest valid substring whose last character is `s[i]`.
    Apparently, the final answer will be "the longest among the longests", i.e.
    `max(|sub(0)|, |sub(1)|, ..., |sub(|s|-1)|)`.

    Now, notice that the "starting position" of `sub(i)` is monotonically increasing regarding `i`!
    Otherwise, imagine `sub(i+1)` started at `j` while `sub(i)` started at `j+1` (or even worse),
    then `sub(i)` could be made longer (by starting at `j` instead).
    This is an obvious contradiction.

    Therefore, when we search for the starting position of `sub(i)` (the `lo`) for each `i` (the `hi`),
    there's no need to "look back".

2. The solution above can be made more efficient, using "jumping window" instead of "sliding window".
  Namely, we use a dict (instead of set) to look up the "position of repetition",
  and move `lo` right after that position at once.

  You can even "early terminate" (based on `lo`) when all remaining intervals are doomed "no longer",
  resulting in even fewer number of loop iterations.
  (Time complexity will still be O(n), though.)

  The corresponding verification code is shown below:
*/


// For verification simplicity, we pretend as if:
// - `map` were Python dict (or even better, a fixed-size array -- if the "alphabet" is small)
method lengthOfLongestSubstring'(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
{}

// Bonus Question:
//   "Why can we safely use (C) instead of (D) as the loop condition? Won't `hi` go out-of-bound?"
// Can you figure it out?


// Kept File 14:
// filename: SENG2011_tmp_tmpgk5jq85q_exam_ex4.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/SENG2011_tmp_tmpgk5jq85q_exam_ex4.dfy
// num_methods: 0
// num_lemmas: 1
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 0
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

lemma {:induction false} Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{}


// Kept File 15:
// filename: dafny-synthesis_task_id_458.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_458.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 2
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{}
// Tossed File 1:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_lib_seq.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_lib_seq.dfy
// num_methods: 1
// num_lemmas: 30
// num_classes: 0
// num_functions: 2
// num_predicates: 7
// num_ensures: 35
// num_requires: 38
// num_lines: 217
// num_no_ensures: 0
// num_no_requires: 6
// num_none_either: 2
// keepToss: TOSS

module Seq {
    export reveals *
    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {}

    predicate substring1<A(==)>(sub: seq<A>, super: seq<A>) {
        exists k :: 0 <= k < |super| && sub <= super[k..]
    }


    ghost predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists xs: seq<A> :: IsSuffix(xs, super) && sub <= xs
    }

    predicate isSubstring<A(==)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists k,j :: 0 <= k < j <= |super| && sub == super[k..j]
    }

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j-k
        ensures xs[k..j][s..t] == xs[(k+s)..(k+s+(t-s))]
    {}



    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {}

    predicate IsSuffix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[|ys| - |xs|..]
    }
    
    predicate IsPrefix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[..|xs|]
    }

    lemma PrefixRest<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures exists yss: seq<T> :: ys == xs + yss && |yss| == |ys|-|xs|;
    {}

    lemma IsSuffixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsSuffix(xs, ys)
        ensures IsPrefix(reverse(xs), reverse(ys))
    {}

    lemma IsPrefixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures IsSuffix(reverse(xs), reverse(ys))
    {}

    lemma IsPrefixReversedAll<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(reverse(xs), reverse(ys))
        ensures IsSuffix(reverse(reverse(xs)), reverse(reverse(ys)))
    {}

    predicate IsSuffix2<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && exists K :: 0 <= K <= |ys|-|xs| && ys == ys[0..K] + xs + ys[(K+|xs|)..]
    }

    function reverse<A>(x: seq<A>): seq<A> 

    {}

    lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>) 
        ensures multiset(xs) == multiset(reverse(xs))
    {}

    lemma  reversePreservesLength<A>(xs: seq<A>)
        ensures |xs| == |reverse(xs)|
    {

    }

    lemma  lastReverseIsFirst<A>(xs: seq<A>)
        requires |xs| > 0
        ensures xs[0] == reverse(xs)[|reverse(xs)|-1]
    {}

    lemma firstReverseIsLast<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs)[0] == xs[|xs|-1]
    {

    }

    lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
    {}


    lemma reverseRest<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs) == [xs[ |xs| -1 ] ] + reverse(xs[0..|xs|-1])
    {}

    lemma ReverseIndexAll<T>(xs: seq<T>)
        ensures |reverse(xs)| == |xs|
        ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
    {}

    lemma ReverseIndex<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[i] == xs[|xs| - i - 1]
    {}
    lemma ReverseIndexBack<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[|xs| - i - 1] == xs[i]
    {}

    lemma ReverseSingle<A>(xs: seq<A>) 
        requires |xs| == 1
        ensures reverse(xs) == xs
    {

    }

    lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
        requires |xs| == |ys|
        requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
        ensures xs == ys
    {
    }

    lemma reverseReverseIdempotent<A>(xs: seq<A>) 
        ensures reverse(reverse(xs)) == xs
    {}

    lemma notInNotEqual<A>(xs: seq<A>, elem: A)
        requires elem !in xs
        ensures forall k :: 0 <= k < |xs| ==> xs[k] != elem
    {

    }

    predicate distinct<A(==)>(s: seq<A>) {
        forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
    }

    lemma distincts<A>(xs: seq<A>, ys: seq<A>)
        requires distinct(xs)
        requires distinct(ys)
        requires forall x :: x in xs ==> x !in ys 
        requires forall y :: y in ys ==> y !in xs 
        ensures distinct(xs+ys)
    {}

    lemma reverseDistinct<A>(list: seq<A>)
        requires distinct(list)
        ensures distinct(reverse(list))
    {}

    lemma distinctSplits<A>(list: seq<A>)
        requires distinct(list)
        ensures forall i :: 1 <= i < |list| ==> distinct(list[..i])
    {}

    lemma multisetItems<A>(list: seq<A>, item: A)
        requires item in list
        requires multiset(list)[item] > 1
        ensures exists i,j :: 0 <= i < j < |list| && list[i] == item && list[j] == item && i != j
    {}

    lemma distinctMultisetIs1<A>(list: seq<A>, item: A) 
        requires distinct(list)
        requires item in list
        ensures multiset(list)[item] == 1
    {}

    lemma indistinctMultisetIsGreaterThan1<A>(list: seq<A>) 
        requires !distinct(list)
        ensures exists item :: multiset(list)[item] > 1
    {}

    lemma multisetIsGreaterThan1Indistinct<A>(list: seq<A>) 
        requires exists item :: multiset(list)[item] > 1
        ensures !distinct(list)
    {}

    lemma indistinctPlusX<A>(items: seq<A>, x: A)
        requires !distinct(items)
        ensures forall i :: 0 <= i < |items| ==> !distinct(items[..i]+[x]+items[i..])
    {}

    lemma pigeonHolesMultiset<A>(items: set<A>, list: seq<A>, n: nat)
        requires |items| == n
        requires forall x :: x in list ==> x in items
        requires |list| > n
        ensures exists item :: multiset(list)[item] > 1
    {}

    lemma pigeonHoles<A>(items: set<A>, list: seq<A>, n: nat)
        requires |items| == n
        requires forall x :: x in list ==> x in items
        requires |list| > n
        ensures !distinct(list)
    {}

    lemma reverseInitList<T>(xs: seq<T>)
        requires |xs| > 1
        requires |reverse(xs)| == |xs|
        ensures reverse(reverse(xs)[..|xs|-1]) == xs[1..]
    {}
    
    method SeqTest() {}

}



// Tossed File 2:
// filename: WrappedEther.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/WrappedEther.dfy
// num_methods: 0
// num_lemmas: 3
// num_classes: 0
// num_functions: 19
// num_predicates: 0
// num_ensures: 7
// num_requires: 11
// num_lines: 263
// num_no_ensures: 9
// num_no_requires: 6
// num_none_either: 6
// keepToss: TOSS
/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
module Int {
    const TWO_7   : int := 0x0_80
    const TWO_8   : int := 0x1_00
    const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    const TWO_24  : int := 0x1_0000_00
    const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    const TWO_40  : int := 0x1_0000_0000_00
    const TWO_48  : int := 0x1_0000_0000_0000
    const TWO_56  : int := 0x1_0000_0000_0000_00
    const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Signed Integers
    const MIN_I8   : int := -TWO_7
    const MAX_I8   : int :=  TWO_7 - 1
    const MIN_I16  : int := -TWO_15
    const MAX_I16  : int :=  TWO_15 - 1
    const MIN_I32  : int := -TWO_31
    const MAX_I32  : int :=  TWO_31 - 1
    const MIN_I64  : int := -TWO_63
    const MAX_I64  : int :=  TWO_63 - 1
    const MIN_I128 : int := -TWO_127
    const MAX_I128 : int :=  TWO_127 - 1
    const MIN_I256 : int := -TWO_255
    const MAX_I256 : int :=  TWO_255 - 1

    newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
    newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
    newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
    newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
    newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
    newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

    // Unsigned Integers
    const MAX_U8 : int :=  TWO_8 - 1
    const MAX_U16 : int := TWO_16 - 1
    const MAX_U24 : int := TWO_24 - 1
    const MAX_U32 : int := TWO_32 - 1
    const MAX_U40 : int := TWO_40 - 1
    const MAX_U48 : int := TWO_48 - 1
    const MAX_U56 : int := TWO_56 - 1
    const MAX_U64 : int := TWO_64 - 1
    const MAX_U128 : int := TWO_128 - 1
    const MAX_U160: int := TWO_160 - 1
    const MAX_U256: int := TWO_256 - 1

    newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
    newtype{} u16 = i:int | 0 <= i <= MAX_U16
    newtype{:nativeType "uint"} u24 = i:int | 0 <= i <= MAX_U24
    newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
    newtype{:nativeType "ulong"} u40 = i:int   | 0 <= i <= MAX_U40
    newtype{:nativeType "ulong"} u48 = i:int   | 0 <= i <= MAX_U48
    newtype{:nativeType "ulong"} u56 = i:int   | 0 <= i <= MAX_U56
    newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
    newtype u128 = i:int | 0 <= i <= MAX_U128
    newtype u160 = i:int | 0 <= i <= MAX_U160
    newtype u256 = i:int | 0 <= i <= MAX_U256


    // Determine maximum of two u256 integers.
    function Max(i1: int, i2: int) : int {}

    // Determine maximum of two u256 integers.
    function Min(i1: int, i2: int) : int {}

    // Round up a given number (i) by a given multiple (r).
    function RoundUp(i: int, r: nat) : int
    requires r > 0 {}

    // Return the maximum value representable using exactly n unsigned bytes.
    // This is essentially computing (2^n - 1).  However, the point of doing it
    // in this fashion is to avoid using Pow() as this is challenging for the
    // verifier.
    function MaxUnsignedN(n:nat) : (r:nat)
    requires 1 <= n <= 32 {}


    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {}

    // Simple lemma about POW.
    lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {}

    // =========================================================
    // Non-Euclidean Division / Remainder
    // =========================================================

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: int, rhs: int) : int
    requires rhs != 0 {}

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function Rem(lhs: int, rhs: int) : int
    requires rhs != 0 {}
}

/**
 * Various helper methods related to unsigned 8bit integers.
 */
module U8 {}

/**
 * Various helper methods related to unsigned 16bit integers.
 */
module U16 {}

/**
 * Various helper methods related to unsigned 32bit integers.
 */
module U32 {}

/**
 * Various helper methods related to unsigned 64bit integers.
 */
module U64 {}

/**
 * Various helper methods related to unsigned 128bit integers.
 */
module U128 {}

/**
 * Various helper methods related to unsigned 256bit integers.
 */
module U256 {
    import opened Int
    import U8
    import U16
    import U32
    import U64
    import U128

    /** An axiom stating that a bv256 converted as a nat is bounded by 2^256. */
    lemma {:axiom} as_bv256_as_u256(v: bv256)
        ensures v as nat < TWO_256

    function Shl(lhs: u256, rhs: u256) : u256
    {}

    function Shr(lhs: u256, rhs: u256) : u256 {}

    /**
     * Compute the log of a value at base 2, where the result in rounded down.
     * This effectively determines the position of the highest on bit.
     */
    function Log2(v:u256) : (r:nat)
    ensures r < 256 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u256) : (r:nat)
    ensures r <= 31 {}

    // Read nth 128bit word out of this u256, where 0 identifies the most
    // significant word.
    function NthUint128(v:u256, k: nat) : u128
        // Cannot read more than two words!
        requires k < 2 {}

    // Read nth byte out of this u256, where 0 identifies the most
    // significant byte.
    function NthUint8(v:u256, k: nat) : u8
    // Cannot read more than 32bytes!
    requires k < 32 {}

    function Read(bytes: seq<u8>, address:nat) : u256
    requires (address+31) < |bytes| {}

    /**
     * Convert a u256 into a sequence of 32bytes in big endian representation.
     */
    function ToBytes(v:u256) : (r:seq<u8>)
    ensures |r| == 32 {}

    /**
     *
     */
    function SignExtend(v: u256, k: nat) : u256 {}
}

module I256 {
    import U256
    import Word
    import opened Int

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0
        // Range restriction to prevent overflow
        requires (rhs != -1 || lhs != (-TWO_255 as i256)) {}

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function Rem(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0 {}

    /**
     *  Shifting 1 left less than 256 times produces a non-zero value.
     *
     *  More generally, shifting-left 1 less than k times over k bits
     *  yield a non-zero number.
     *
     *  @example    over 2 bits, left-shift 1 once: 01 -> 10
     *  @example    over 4 bits, left-shift 1 3 times: 0001 -> 0010 -> 0100 -> 1000
     */
    lemma ShiftYieldsNonZero(x: u256)
        requires 0 < x < 256
        ensures U256.Shl(1, x) > 0
    {}

    // Shift Arithmetic Right.  This implementation follows the Yellow Paper quite
    // accurately.
    function Sar(lhs: i256, rhs: u256): i256 {}
}

module Word {}




// Tossed File 3:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_leetcode_stairClimbing.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_leetcode_stairClimbing.dfy
// num_methods: 2
// num_lemmas: 14
// num_classes: 0
// num_functions: 5
// num_predicates: 2
// num_ensures: 20
// num_requires: 13
// num_lines: 120
// num_no_ensures: 0
// num_no_requires: 8
// num_none_either: 4
// keepToss: TOSS
/*
You are climbing a staircase. It takes n steps to reach the top.

Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top?
function climbStairs(n: number): number {};
*/

datatype Steps = One | Two

function stepSum(xs: seq<Steps>): nat {}

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {
    stepSum(xs) == n
}
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}

lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 0
{}
lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{}

lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{}

ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{}

lemma SeqsNotEqualImplication<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures (exists i: nat :: i < |xs| && i <|ys| && xs[i] != ys[i]) || |xs| < |ys| || |ys| < |xs|
{}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{}

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{

}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss+sz, sum)
{

}

ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{}

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{}

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{

}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>) 
    requires sx !! sy
    requires sz == sx + sy
    ensures |sx + sy| == |sx| + |sy|
    ensures |sz| == |sx| + |sy|
{

}

lemma stepSetsAdd(i: nat, steps: array<nat>) 
    requires i >= 2
    requires steps.Length >= i+1
    requires forall k: nat :: k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    ensures exists sp : set< seq<Steps> > :: |sp| == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{}

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{}


method Test() {}



// Tossed File 4:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_triggers_large-quantifiers-dont-break-dafny.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_triggers_large-quantifiers-dont-break-dafny.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 50
// num_ensures: 0
// num_requires: 0
// num_lines: 63
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 1
// keepToss: TOSS
// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test ensures that the trigger  collector (the routine that picks trigger
// candidates) does not  actually consider all subsets of terms;  if it did, the
// following would take horribly long

predicate P0(x: bool)
predicate P1(x: bool)
predicate P2(x: bool)
predicate P3(x: bool)
predicate P4(x: bool)
predicate P5(x: bool)
predicate P6(x: bool)
predicate P7(x: bool)
predicate P8(x: bool)
predicate P9(x: bool)
predicate P10(x: bool)
predicate P11(x: bool)
predicate P12(x: bool)
predicate P13(x: bool)
predicate P14(x: bool)
predicate P15(x: bool)
predicate P16(x: bool)
predicate P17(x: bool)
predicate P18(x: bool)
predicate P19(x: bool)
predicate P20(x: bool)
predicate P21(x: bool)
predicate P22(x: bool)
predicate P23(x: bool)
predicate P24(x: bool)
predicate P25(x: bool)
predicate P26(x: bool)
predicate P27(x: bool)
predicate P28(x: bool)
predicate P29(x: bool)
predicate P30(x: bool)
predicate P31(x: bool)
predicate P32(x: bool)
predicate P33(x: bool)
predicate P34(x: bool)
predicate P35(x: bool)
predicate P36(x: bool)
predicate P37(x: bool)
predicate P38(x: bool)
predicate P39(x: bool)
predicate P40(x: bool)
predicate P41(x: bool)
predicate P42(x: bool)
predicate P43(x: bool)
predicate P44(x: bool)
predicate P45(x: bool)
predicate P46(x: bool)
predicate P47(x: bool)
predicate P48(x: bool)
predicate P49(x: bool)

method M() {
  assert forall x :: true || P0(x) || P1(x) || P2(x) || P3(x) || P4(x) || P5(x) || P6(x) || P7(x) || P8(x) || P9(x) || P10(x) || P11(x) || P12(x) || P13(x) || P14(x) || P15(x) || P16(x) || P17(x) || P18(x) || P19(x) || P20(x) || P21(x) || P22(x) || P23(x) || P24(x) || P25(x) || P26(x) || P27(x) || P28(x) || P29(x) || P30(x) || P31(x) || P32(x) || P33(x) || P34(x) || P35(x) || P36(x) || P37(x) || P38(x) || P39(x) || P40(x) || P41(x) || P42(x) || P43(x) || P44(x) || P45(x) || P46(x) || P47(x) || P48(x) || P49(x);
}




// Tossed File 5:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug92.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug92.dfy
// num_methods: 0
// num_lemmas: 9
// num_classes: 0
// num_functions: 6
// num_predicates: 0
// num_ensures: 0
// num_requires: 15
// num_lines: 68
// num_no_ensures: 9
// num_no_requires: 0
// num_none_either: 6
// keepToss: TOSS
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module ModOpaque {
    function {:opaque} Hidden(x:int) : (int, int)
    {}

    function Visible(x:int) : (int, int)
    {}

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {}

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}
}

module ModVisible {
    function Hidden(x:int) : (int, int)
    {}

    function Visible(x:int) : (int, int)
    {}

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {}

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}
}

module ModFuel {
    function {:fuel 0,0} Hidden(x:int) : (int, int)
    {}

    function Visible(x:int) : (int, int)
    {}

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {}

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {}
}



// Tossed File 6:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny4_NipkowKlein-chapter3.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny4_NipkowKlein-chapter3.dfy
// num_methods: 0
// num_lemmas: 8
// num_classes: 0
// num_functions: 13
// num_predicates: 0
// num_ensures: 7
// num_requires: 0
// num_lines: 109
// num_no_ensures: 0
// num_no_requires: 7
// num_none_either: 14
// keepToss: TOSS
// RUN: %dafny /proverOpt:O:smt.qi.eager_threshold=30 /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is a Dafny encoding of chapter 3 from "Concrete Semantics: With Isabelle/HOL" by
// Tobias Nipkow and Gerwin Klein.

// ----- lists -----

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function append(xs: List, ys: List): List
{}

// ----- arithmetic expressions -----

type vname = string  // variable names
datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)  // arithmetic expressions

type val = int
type state = vname -> val

ghost function aval(a: aexp, s: state): val
{}

lemma Example0()
{}

// ----- constant folding -----

ghost function asimp_const(a: aexp): aexp
{}

lemma AsimpConst(a: aexp, s: state)
  ensures aval(asimp_const(a), s) == aval(a, s)
{}

// more constant folding

ghost function plus(a0: aexp, a1: aexp): aexp
{}

lemma AvalPlus(a0: aexp, a1: aexp, s: state)
  ensures aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s)
{}

ghost function asimp(a: aexp): aexp
{}

lemma AsimpCorrect(a: aexp, s: state)
  ensures aval(asimp(a), s) == aval(a, s)
{}

// The following lemma is not in the Nipkow and Klein book, but it's a fun one to prove.
lemma ASimplInvolutive(a: aexp)
  ensures asimp(asimp(a)) == asimp(a)
{
}

// ----- boolean expressions -----

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

ghost function bval(b: bexp, s: state): bool
{}

// constant folding for booleans

ghost function not(b: bexp): bexp
{}

ghost function and(b0: bexp, b1: bexp): bexp
{}

ghost function less(a0: aexp, a1: aexp): bexp
{}

ghost function bsimp(b: bexp): bexp
{}

lemma BsimpCorrect(b: bexp, s: state)
  ensures bval(bsimp(b), s) == bval(b, s)
{}

// ----- stack machine -----

datatype instr = LOADI(val) | LOAD(vname) | ADD

type stack = List<val>

ghost function exec1(i: instr, s: state, stk: stack): stack
{}

ghost function exec(ii: List<instr>, s: state, stk: stack): stack
{}

// ----- compilation -----

ghost function comp(a: aexp): List<instr>
{}

lemma CorrectCompilation(a: aexp, s: state, stk: stack)
  ensures exec(comp(a), s, stk) == Cons(aval(a, s), stk)
{}

lemma ExecAppend(ii0: List<instr>, ii1: List<instr>, s: state, stk: stack)
  ensures exec(append(ii0, ii1), s, stk) == exec(ii1, s, exec(ii0, s, stk))
{}




// Tossed File 7:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_InfiniteTrees.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_InfiniteTrees.dfy
// num_methods: 0
// num_lemmas: 31
// num_classes: 0
// num_functions: 12
// num_predicates: 14
// num_ensures: 33
// num_requires: 18
// num_lines: 379
// num_no_ensures: 0
// num_no_requires: 14
// num_none_either: 11
// keepToss: TOSS
// RUN: %dafny /compile:0 /deprecation:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is the usual definition of possibly infinite lists, along with a function Tail(s, n), which drops
// n heads from s, and two lemmas that prove properties of Tail.

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function Tail(s: Stream, n: nat): Stream
{}

lemma Tail_Lemma0(s: Stream, n: nat)
  requires s.Cons? && Tail(s, n).Cons?;
  ensures Tail(s, n).tail == Tail(s.tail, n);
{
}
lemma Tail_Lemma1(s: Stream, k: nat, n: nat)
  requires k <= n;
  ensures Tail(s, n).Cons? ==> Tail(s, k).Cons?;
  // Note, the contrapositive of this lemma says:  Tail(s, k) == Nil ==> Tail(s, n) == Nil
{}
lemma Tail_Lemma2(s: Stream, n: nat)
  requires s.Cons? && Tail(s.tail, n).Cons?;
  ensures Tail(s, n).Cons?;
{}

// Co-predicate IsNeverEndingStream(s) answers whether or not s ever contains Nil.

greatest predicate IsNeverEndingStream<S>(s: Stream<S>)
{
  match s
  case Nil => false
  case Cons(_, tail) => IsNeverEndingStream(tail)
}

// Here is an example of an infinite stream.

ghost function AnInfiniteStream(): Stream<int>
{}
greatest lemma Proposition0()
  ensures IsNeverEndingStream(AnInfiniteStream());
{
}

// Now, consider a Tree definition, where each node can have a possibly infinite number of children.

datatype Tree = Node(children: Stream<Tree>)

// Such a tree might have not just infinite width but also infinite height.  The following predicate
// holds if there is, for every path down from the root, a common bound on the height of each such path.
// Note that the definition needs a co-predicate in order to say something about all of a node's children.

ghost predicate HasBoundedHeight(t: Tree)
{
  exists n :: 0 <= n && LowerThan(t.children, n)
}
greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case Nil => true
  case Cons(t, tail) =>
    1 <= n && LowerThan(t.children, n-1) && LowerThan(tail, n)
}

// Co-predicate LowerThan(s, n) recurses on LowerThan(s.tail, n).  Thus, a property of LowerThan is that
// LowerThan(s, h) implies LowerThan(s', h) for any suffix s' of s.

lemma LowerThan_Lemma(s: Stream<Tree>, n: nat, h: nat)
  ensures LowerThan(s, h) ==> LowerThan(Tail(s, n), h);
{}

// A tree t where every node has an infinite number of children satisfies InfiniteEverywhere(t.children).
// Otherwise, IsFiniteSomewhere(t) holds.  That is, IsFiniteSomewhere says that the tree has some node
// with less than infinite width.  Such a tree may or may not be of finite height, as we'll see in an
// example below.

ghost predicate IsFiniteSomewhere(t: Tree)
{
  !InfiniteEverywhere(t.children)
}
greatest predicate InfiniteEverywhere(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteEverywhere(t.children) && InfiniteEverywhere(tail)
}

// Here is a tree where every node has exactly 1 child.  Such a tree is finite in width (which implies
// it is finite somewhere) and infinite in height (which implies there is no bound on its height).

ghost function SkinnyTree(): Tree
{}
lemma Proposition1()
  ensures IsFiniteSomewhere(SkinnyTree()) && !HasBoundedHeight(SkinnyTree());
{}

// Any tree where all paths have bounded height are finite somewhere.

lemma Theorem0(t: Tree)
  requires HasBoundedHeight(t);
  ensures IsFiniteSomewhere(t);
{}
lemma FindNil(s: Stream<Tree>, n: nat) returns (k: nat)
  requires LowerThan(s, n);
  ensures !InfiniteEverywhere#[k as ORDINAL](s);
{}

// We defined an InfiniteEverywhere property above and negated it to get an IsFiniteSomewhere predicate.
// If we had an InfiniteHeightSomewhere property, then we could negate it to obtain a predicate
// HasFiniteHeightEverywhere.  Consider the following definitions:

ghost predicate HasFiniteHeightEverywhere_Bad(t: Tree)
{
  !InfiniteHeightSomewhere_Bad(t.children)
}
greatest predicate InfiniteHeightSomewhere_Bad(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteHeightSomewhere_Bad(t.children) || InfiniteHeightSomewhere_Bad(tail)
}

// In some ways, this definition may look reasonable--a list of trees is infinite somewhere
// if it is nonempty, and either the list of children of the first node satisfies the property
// or the tail of the list does.  However, because co-predicates are defined by greatest
// fix-points, there is nothing in this definition that "forces" the list to ever get to a
// node whose list of children satisfy the property.  The following example shows that a
// shallow, infinitely wide tree satisfies the negation of HasFiniteHeightEverywhere_Bad.

ghost function ATree(): Tree
{}
ghost function ATreeChildren(): Stream<Tree>
{}
lemma Proposition2()
  ensures !HasFiniteHeightEverywhere_Bad(ATree());
{}
greatest lemma Proposition2_Lemma0()
  ensures IsNeverEndingStream(ATreeChildren());
{
}
greatest lemma Proposition2_Lemma1(s: Stream<Tree>)
  requires IsNeverEndingStream(s);
  ensures InfiniteHeightSomewhere_Bad(s);
{}

// What was missing from the InfiniteHeightSomewhere_Bad definition was the existence of a child
// node that satisfies the property recursively.  To address that problem, we may consider
// a definition like the following:

/*
ghost predicate HasFiniteHeightEverywhere_Attempt(t: Tree)
{
  !InfiniteHeightSomewhere_Attempt(t.children)
}
greatest predicate InfiniteHeightSomewhere_Attempt(s: Stream<Tree>)
{
  exists n ::
    0 <= n &&
    var ch := Tail(s, n);
    ch.Cons? && InfiniteHeightSomewhere_Attempt(ch.head.children)
}
*/

// However, Dafny does not allow this definition:  the recursive call to InfiniteHeightSomewhere_Attempt
// sits inside an unbounded existential quantifier, which means the co-predicate's connection with its prefix
// predicate is not guaranteed to hold, so Dafny disallows this co-predicate definition.

// We will use a different way to express the HasFiniteHeightEverywhere property.  Instead of
// using an existential quantifier inside the recursively defined co-predicate, we can place a "larger"
// existential quantifier outside the call to the co-predicate.  This existential quantifier is going to be
// over the possible paths down the tree (it is "larger" in the sense that it selects a child tree at each
// level down the path, not just at one level).

// A path is a possibly infinite list of indices, each selecting the next child tree to navigate to.  A path
// is valid when it uses valid indices and does not stop at a node with children.

greatest predicate ValidPath(t: Tree, p: Stream<int>)
{
  match p
  case Nil => t == Node(Nil)
  case Cons(index, tail) =>
    0 <= index &&
    var ch := Tail(t.children, index);
    ch.Cons? && ValidPath(ch.head, tail)
}
lemma ValidPath_Lemma(p: Stream<int>)
  ensures ValidPath(Node(Nil), p) ==> p == Nil;
{}

// A tree has finite height (everywhere) if it has no valid infinite paths.

ghost predicate HasFiniteHeight(t: Tree)
{
  forall p :: ValidPath(t, p) ==> !IsNeverEndingStream(p)
}

// From this definition, we can prove that any tree of bounded height is also of finite height.

lemma Theorem1(t: Tree)
  requires HasBoundedHeight(t);
  ensures HasFiniteHeight(t);
{}
lemma Theorem1_Lemma(t: Tree, n: nat, p: Stream<int>)
  requires LowerThan(t.children, n) && ValidPath(t, p);
  ensures !IsNeverEndingStream(p);
  decreases n;
{}

// In fact, HasBoundedHeight is strictly strong than HasFiniteHeight, as we'll show with an example.
// Define SkinnyFiniteTree(n) to be a skinny (that is, of width 1) tree of height n.

ghost function SkinnyFiniteTree(n: nat): Tree
  ensures forall k: nat :: LowerThan(SkinnyFiniteTree(n).children, k) <==> n <= k;
{}

// Next, we define a tree whose root has an infinite number of children, child i of which
// is a SkinnyFiniteTree(i).

ghost function FiniteUnboundedTree(): Tree
{}
ghost function EverLongerSkinnyTrees(n: nat): Stream<Tree>
{}

lemma EverLongerSkinnyTrees_Lemma(k: nat, n: nat)
  ensures Tail(EverLongerSkinnyTrees(k), n).Cons?;
  ensures Tail(EverLongerSkinnyTrees(k), n).head == SkinnyFiniteTree(k+n);
  decreases n;
{}

lemma Proposition3()
  ensures !HasBoundedHeight(FiniteUnboundedTree()) && HasFiniteHeight(FiniteUnboundedTree());
{}
lemma Proposition3a()
  ensures !HasBoundedHeight(FiniteUnboundedTree());
{}
lemma Proposition3b()
  ensures HasFiniteHeight(FiniteUnboundedTree());
{}
lemma Proposition3b_Lemma(t: Tree, h: nat, p: Stream<int>)
  requires LowerThan(t.children, h) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
  decreases h
{}

// Using a stream of integers to denote a path is convenient, because it allows us to
// use Tail to quickly select the next child tree.  But we can also define paths in a
// way that more directly follows the navigation steps required to get to the next child,
// using Peano numbers instead of the built-in integers.  This means that each Succ
// constructor among the Peano numbers corresponds to moving "right" among the children
// of a tree node.  A path is valid only if it always selects a child from a list
// of children; this implies we must avoid infinite "right" moves.  The appropriate type
// Numbers (which is really just a stream of natural numbers) is defined as a combination
// two mutually recursive datatypes, one inductive and the other co-inductive.

codatatype CoOption<T> = None | Some(get: T)
datatype Number = Succ(Number) | Zero(CoOption<Number>)

// Note that the use of an inductive datatype for Number guarantees that sequences of successive
// "right" moves are finite (analogously, each Peano number is finite).  Yet the use of a co-inductive
// CoOption in between allows paths to go on forever.  In contrast, a definition like:

codatatype InfPath = Right(InfPath) | Down(InfPath) | Stop

// does not guarantee the absence of infinitely long sequences of "right" moves.  In other words,
// InfPath also gives rise to indecisive paths--those that never select a child node.  Also,
// compare the definition of Number with:

codatatype FinPath = Right(FinPath) | Down(FinPath) | Stop

// where the type can only represent finite paths.  As a final alternative to consider, had we
// wanted only infinite, decisive paths, we would just drop the None constructor, forcing each
// CoOption to be some Number.  As it is, we want to allow both finite and infinite paths, but we
// want to be able to distinguish them, so we define a co-predicate that does so:

greatest predicate InfinitePath(r: CoOption<Number>)
{
  match r
  case None => false
  case Some(num) => InfinitePath'(num)
}
greatest predicate InfinitePath'(num: Number)
{
  match num
  case Succ(next) => InfinitePath'(next)
  case Zero(r) => InfinitePath(r)
}

// As before, a path is valid for a tree when it navigates to existing nodes and does not stop
// in a node with more children.

greatest predicate ValidPath_Alt(t: Tree, r: CoOption<Number>)
{
  match r
  case None => t == Node(Nil)
  case Some(num) => ValidPath_Alt'(t.children, num)
}
greatest predicate ValidPath_Alt'(s: Stream<Tree>, num: Number)
{
  match num
  case Succ(next) => s.Cons? && ValidPath_Alt'(s.tail, next)
  case Zero(r) => s.Cons? && ValidPath_Alt(s.head, r)
}

// Here is the alternative definition of a tree that has finite height everywhere, using the
// new paths.

ghost predicate HasFiniteHeight_Alt(t: Tree)
{
  forall r :: ValidPath_Alt(t, r) ==> !InfinitePath(r)
}

// We will prove that this new definition is equivalent to the previous.  To do that, we
// first definite functions S2N and N2S to map between the path representations
// Stream<int> and CoOption<Number>, and then prove some lemmas about this correspondence.

ghost function S2N(p: Stream<int>): CoOption<Number>
  decreases 0;
{}
ghost function S2N'(n: nat, tail: Stream<int>): Number
  decreases n + 1;
{}

ghost function N2S(r: CoOption<Number>): Stream<int>
{}
ghost function N2S'(n: nat, num: Number): Stream<int>
  decreases num;
{}

lemma Path_Lemma0(t: Tree, p: Stream<int>)
  requires ValidPath(t, p);
  ensures ValidPath_Alt(t, S2N(p));
{}
greatest lemma Path_Lemma0'(t: Tree, p: Stream<int>)
  requires ValidPath(t, p);
  ensures ValidPath_Alt(t, S2N(p));
{}
greatest lemma Path_Lemma0''(tChildren: Stream<Tree>, n: nat, tail: Stream<int>)
  requires var ch := Tail(tChildren, n); ch.Cons? && ValidPath(ch.head, tail);
  ensures ValidPath_Alt'(tChildren, S2N'(n, tail));
{}
lemma Path_Lemma1(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r);
  ensures ValidPath(t, N2S(r));
{}
greatest lemma Path_Lemma1'(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r);
  ensures ValidPath(t, N2S(r));
  decreases 1;
{}
greatest lemma Path_Lemma1''(s: Stream<Tree>, n: nat, num: Number)
  requires ValidPath_Alt'(Tail(s, n), num);
  ensures ValidPath(Node(s), N2S'(n, num));
  decreases 0, num;
{}
lemma Path_Lemma2(p: Stream<int>)
  ensures IsNeverEndingStream(p) ==> InfinitePath(S2N(p));
{}
greatest lemma Path_Lemma2'(p: Stream<int>)
  requires IsNeverEndingStream(p);
  ensures InfinitePath(S2N(p));
{}
greatest lemma Path_Lemma2''(p: Stream<int>, n: nat, tail: Stream<int>)
  requires IsNeverEndingStream(p) && p.tail == tail
  ensures InfinitePath'(S2N'(n, tail))
{}
lemma Path_Lemma3(r: CoOption<Number>)
  ensures InfinitePath(r) ==> IsNeverEndingStream(N2S(r));
{}
greatest lemma Path_Lemma3'(n: nat, num: Number)
  requires InfinitePath'(num);
  ensures IsNeverEndingStream(N2S'(n, num));
  decreases num;
{}

lemma Theorem2(t: Tree)
  ensures HasFiniteHeight(t) <==> HasFiniteHeight_Alt(t);
{}




// Tossed File 8:
// filename: BPTree-verif_tmp_tmpq1z6xm1d_Utils.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/BPTree-verif_tmp_tmpq1z6xm1d_Utils.dfy
// num_methods: 3
// num_lemmas: 9
// num_classes: 0
// num_functions: 3
// num_predicates: 7
// num_ensures: 17
// num_requires: 25
// num_lines: 361
// num_no_ensures: 1
// num_no_requires: 2
// num_none_either: 4
// keepToss: TOSS

// method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
// //   ensures count == |set i | i in numbers && i < threshold|
//     ensures count == |SetLessThan(numbers, threshold)|
// {}

function SetLessThan(numbers: set<int>, threshold: int): set<int>
{}

method Main()
{}

lemma set_memebrship_implies_cardinality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures |s| == |t|
  decreases s_size {}


lemma set_memebrship_implies_cardinality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures |s| == |t| {}


/*
lemma Bijection(arr: seq<int>, s: set<int>) // returns (bool)
  requires sorted(arr)
  // requires forall x, y :: x in s && y in s && x != y ==> x < y
  ensures  |s| == |arr|
{}
*/

function seqSet(nums: seq<int>, index: nat): set<int> {}

lemma containsDuplicateI(nums: seq<int>) returns (containsDuplicate: bool)
    ensures containsDuplicate ==>  exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
{
    var windowGhost: set<int> := {};
    var windowSet: set<int> := {};
    for i:= 0 to |nums| 
        invariant 0 <= i <= |nums|
        invariant forall j :: 0 <= j < i < |nums|  ==> nums[j] in windowSet
        // invariant forall x :: x in windowSet ==> x in nums
        invariant forall x :: x in windowSet ==> x in nums[0..i]
        invariant seqSet(nums, i) <= windowSet
    {
        windowGhost := windowSet;
        if nums[i] in windowSet { // does not verify
        // if nums[i] in seqSet(nums, i) { //verifies
            return true;
        }
        windowSet := windowSet + {nums[i]};
    }
    return false;
}

// lemma numElemsOfSet(a: seq<int>)
//   requires sorted(a)
// {
//   assert distinct(a);
//   var s := set x | x in a;
//   assert forall x :: x in s ==> x in a[..];
//   assert forall x :: x in a ==> x in s;
//   assert |s| == |a|;
// }

// lemma CardinalitySetEqualsArray(a: seq<int>, s: set<int>)
//   requires s == set x | x in a
//   requires distinct(a)
//   ensures |s| == |a|
// {
//     assert forall x :: x in s ==> exists i :: 0 <= i < |a| && a[i] == x;
//     assert forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j];
//     // Assert that each element in the array is in the set
//     assert forall i :: 0 <= i < |a| ==> a[i] in s;
//     // Assert that the set contains exactly the elements in the array
//     assert s == set x | x in a;
//     // Assert that the set is a subset of the array
//     assert forall x :: x in s <==> x in a;

//     // Conclude the equivalence
//     assert |s| == |a|;
// }


/*
lemma memebrship_implies_cardinality_helper<A>(s: set<A>, t: seq<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  requires forall i, j :: (0 <= i < |t| && 0 <= j < |t| && i != j ) ==> t[i] != t[j]
  requires |set x | x in t| == |t| 
  ensures |s| == |t|
  decreases s_size {
    if s_size == 0 {
    } else {
      var t_hd;
      t_hd := t[0];
      assert t_hd in s;
      ghost var t_h := set x | x in t[1..];
      assert |t_h| == |t[1..]|; 
      memebrship_implies_cardinality_helper(s - {t_hd}, t[1..], s_size - 1);
    }
}


lemma memebrship_implies_cardinality<A>(s: set<A>, t: seq<A>)
  requires forall x :: x in s <==> x in t
  ensures |s| == |t| {
    memebrship_implies_cardinality_helper(s, t, |s|);
}
*/

lemma set_memebrship_implies_equality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures s == t
  decreases s_size {
  if s_size == 0 {
  } else {
    var s_hd;
    // assign s_hd to a value *such that* s_hd is in s (see such_that expressions)
    s_hd :| s_hd in s;
    set_memebrship_implies_equality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
}


lemma set_memebrship_implies_equality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures s == t {
  set_memebrship_implies_equality_helper(s, t, |s|);
}

// TODO play with this for keys==Contents
lemma set_seq_equality(s: set<int>, t: seq<int>)
  requires distinct(t)
  requires forall x :: x in t <==> x in s
{
  var s2 : set<int> := set x | x in t;
  set_memebrship_implies_equality_helper(s, s2, |s|);
  assert |s2| == |s|;
  // assert |s2| == |t|;
  // assert |s| == |t|;
}


ghost predicate SortedSeq(a: seq<int>)
  //sequence is sorted from left to right
{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
  // get index so that array stays sorted
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  ensures 0<= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx-1]< x
  ensures idx < limit ==> x < a[idx]
{
  idx := limit;
  for i := 0 to limit
    invariant i>0 ==> x > a[i-1]
  {
    if x < a[i] {
      idx := i;
      break;
    }
  }
}

predicate sorted(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate distinct(a: seq<int>)
{
  forall i,j :: (0 <= i < |a| && 0 <= j < |a| && i != j) ==> a[i] != a[j]
}

predicate sorted_eq(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate lessThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] < key
}

predicate greaterThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] > key
}

predicate greaterEqualThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] >= key
}
/*
method InsertSorted(a: array<int>, key: int ) returns (b: array<int>)
  requires sorted_eq(a[..])
  ensures sorted_eq(b[..])
{
  b:= new int[a.Length + 1];

  ghost var k := 0;
  b[0] := key;

  ghost var a' := a[..];

  var i:= 0;
  while (i < a.Length)
    modifies b
    invariant 0 <= k <= i <= a.Length
    invariant b.Length == a.Length + 1
    invariant a[..] == a'
    invariant lessThan(a[..i], key) ==> i == k
    invariant lessThan(a[..k], key)
    invariant b[..k] == a[..k]
    invariant b[k] == key
    invariant k < i ==> b[k+1..i+1] == a[k..i]
    invariant k < i ==> greaterEqualThan(b[k+1..i+1], key)
    invariant 0 <= k < b.Length && b[k] == key
  {
    if(a[i]<key)
    {
      b[i]:= a[i];
      b[i+1] := key;
      k := i+1;
    }
    else if (a[i] >= key)
    {
      b[i+1] := a[i];
    }
    i := i+1;
  }
  assert b[..] == a[..k] + [key] + a[k..];

}
*/

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}


lemma DistributiveIn(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    ensures forall i :: 0 <= i < |a| ==> a[i] in b
{
    assert forall j :: 0 <= j < k ==> a[j] in b;
    assert forall j :: k <= j < |a| ==> a[j] in b;
    assert ((forall j :: 0 <= j < k ==> a[j] in b) && (forall j :: k <= j < |a| ==> a[j] in b)) ==> (forall j :: 0 <= j < |a| ==> a[j] in b);
    assert forall j :: 0 <= j < |a| ==> a[j] in b;
}

lemma DistributiveGreater(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    requires forall j :: 0 <= j < |a| ==> a[j] > 0
    requires key > 0
    ensures forall i :: 0 <= i < |b| ==> b[i] > 0
{
    // assert ((forall j :: 0 <= j < k ==> b[j] > 0) && (forall j :: k <= j < |a| ==> b[j] > 0)) ==> (forall j :: 0 <= j < |b| ==> b[j] > 0);
    assert forall j :: 0 <= j < |b| ==> b[j] > 0;
}

// verifies in more than 45 seconds, but less than 100 seconds
method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
    requires key > 0
    requires key !in a[..]
    requires 0 <= limit < a.Length
    requires forall i :: 0 <= i < limit ==> a[i] > 0
    requires forall i :: limit <= i < a.Length ==> a[i] == 0
    requires sorted(a[..limit]) 
    ensures b.Length == a.Length
    ensures sorted(b[..(limit+ 1)])
    ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
    ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
{
    b:= new int[a.Length];

    ghost var k := 0;
    b[0] := key;

    ghost var a' := a[..];

    var i:= 0;
    while (i < limit)
        modifies b
        invariant 0 <= k <= i <= limit
        invariant b.Length == a.Length
        invariant a[..] == a'
        invariant lessThan(a[..i], key) ==> i == k
        invariant lessThan(a[..k], key)
        invariant b[..k] == a[..k]
        invariant b[k] == key
        invariant k < i ==> b[k+1..i+1] == a[k..i]
        invariant k < i ==> greaterThan(b[k+1..i+1], key)
        invariant 0 <= k < b.Length && b[k] == key
    {
        if(a[i]<key)
        {
            b[i]:= a[i];
            b[i+1] := key;
            k := i+1;
        }
        else if (a[i] >= key)
        {
            b[i+1] := a[i];
        } 
        i := i+1;
    }
    assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    assert sorted(b[..limit+1]);

    // assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    DistributiveIn(a[..limit], b[..limit+1], k, key);
    assert forall i :: 0 <= i < limit ==> a[i] in b[..limit+1];

    DistributiveGreater(a[..limit], b[..limit+1], k, key);
    // assert forall i :: 0 <= i < limit + 1 ==> b[i] > 0;

    ghost var b' := b[..];
    i := limit + 1;
    while i < b.Length 
        invariant limit + 1 <= i <= b.Length 
        invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
        invariant b[..limit+1] == b'[..limit+1]
        invariant sorted(b[..limit+1])
    {
        b[i] := 0;
        i := i + 1;
    }
    assert forall i :: limit + 1 <= i < b.Length ==> b[i] == 0;

}





    



// Tossed File 9:
// filename: Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula5.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula5.dfy
// num_methods: 16
// num_lemmas: 0
// num_classes: 4
// num_functions: 6
// num_predicates: 5
// num_ensures: 39
// num_requires: 29
// num_lines: 304
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: TOSS
/*Ex1 Given the leaky specification of class Set found in Appendix ??, use the techniques from
class (the use of ghost state and dynamic frames) so that the specification no longer leaks
the internal representation. Produce client code that correctly connects to your revised
Set class. */

class Set {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {}
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {}
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {}
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {}
  method Main()
  {}
}

/*2. Using the corrected version of Set as a baseline, implement a PositiveSet class that
enforces the invariant that all numbers in the set are strictly positive. */

class PositiveSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
    && (forall x :: x in elems ==> x > 0)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {}
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {}
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {}
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {}
  method Main()
  {}
}

/*
 * Implement a savings account.
 * A savings account is actually made up of two balances.
 *
 * One is the checking balance, here account owner can deposit and withdraw
 * money at will. There is only one restriction on withdrawing. In a regular
 * bank account, the account owner can make withdrawals as long as he has the
 * balance for it, i.e., the user cannot withdraw more money than the user has.
 * In a savings account, the checking balance can go negative as long as it does
 * not surpass half of what is saved in the savings balance. Consider the
 * following example:
 *
 * Savings = 10
 * Checking = 0
 * Operation 1: withdraw 10 This operation is not valid. Given that the
 * the user only has $$10, his checking account
 * can only decrease down to $$-5 (10/2).
 *
 * Operation 2: withdraw 2 Despite the fact that the checking balance of
 * the user is zero,
 * money in his savings account, therefore, this
 * operation is valid, and the result would be
 * something like:
 * Savings = 10;
 * Checking = -2
 *
 * Regarding depositing money in the savings balance (save), this operation has
 * one small restrictions. It is only possible to save money to the savings
 * balance when the user is not in debt; i.e. to save money into savings, the
 * checking must be non-negative.
 *
 * Given the states:
 * STATE 1 STATE 2
 * Savings = 10 Savings = 10
 * Checking = -5 Checking = 0
 *
 * and the operation save($$60000000000), the operation is valid when executed
 * in STATE 2 but not in STATE 1.
 *
 * Finally, when withdrawing from the savings balance, an operation we will
 * call rescue, the amount the user can withdraw depends on the negativity of
 * the user’s checking account. For instance:
 *
 * Savings: 12
 * Checking: -5
 *
 * In the case, the user could withdraw at most two double dollars ($$). If the
 * user withdrew more than that, the balance of the checking account would
 * go beyond the -50% of the savings account; big no no.
 *
 */

class SavingsAccount {

  var cbalance: int;
  var sbalance: int;

  ghost var Repr:set<object>;

  ghost predicate RepInv()
    reads this,Repr
  {
    this in Repr
    && cbalance >= -sbalance/2
  }

  ghost predicate PositiveChecking()
    reads this,Repr
  {
    cbalance >= 0
  }

  constructor()
    ensures fresh(Repr-{this})
    ensures RepInv()
  {}

  method deposit(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {}

  method withdraw(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {}

  method save(amount: int)
    requires amount > 0
    requires PositiveChecking()
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {}

  method rescue(amount: int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {}
}



/*Ex 4 Change your specification and implementation of the ASet ADT to include a growing
array of integer values. */
class GrowingSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {}
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {}
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr - old(Repr))
  {}
  
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {}
  method Main()
  {}
}




// Tossed File 10:
// filename: dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_PrecedenceLinter.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_PrecedenceLinter.dfy
// num_methods: 6
// num_lemmas: 3
// num_classes: 0
// num_functions: 14
// num_predicates: 51
// num_ensures: 1
// num_requires: 4
// num_lines: 405
// num_no_ensures: 4
// num_no_requires: 1
// num_none_either: 18
// keepToss: TOSS
// RUN: %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P0(A: bool, B: bool, C: bool) {
  A &&
  B ==> C // warning: suspicious lack of parentheses (lhs of ==>)
}

predicate P1(A: bool, B: bool, C: bool) {
  A && B ==>
    C
}

predicate P2(A: bool, B: bool, C: bool) {
  A &&
  B
  ==>
  C
}

predicate P3(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==>
  C &&
  D
}

predicate P4(A: bool, B: bool, C: bool, D: bool) {
    A &&
    B
  ==>
    C &&
    D
}

predicate P5(A: bool, B: bool, C: bool) {
  A ==>
  && B
  && C
}

predicate P6(A: bool, B: bool, C: bool) {
  A ==>
  || B
  || C
}

predicate Q0(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> C && // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
  D
}

predicate Q1(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> C && // warning: suspicious lack of parentheses (lhs of ==>)
        D
}

predicate Q2(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> (C && // warning: suspicious lack of parentheses (lhs of ==>)
  D)
}

predicate Q3(A: bool, B: bool, C: bool, D: bool) {
  (A &&
  B) ==> (C &&
  D)
}

predicate Q4(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> C // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
  && D
}

predicate Q4a(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    C && D
}

predicate Q4b(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    C &&
    D
}

predicate Q4c(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
  && C
  && D
}

predicate Q4d(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    && C
    && D
}

predicate Q5(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> C // warning: suspicious lack of parentheses (lhs of ==>)
           && D
}

predicate Q6(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> && C // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
           && D
}

predicate Q7(A: bool, B: bool, C: bool, D: bool) {
  A
  ==> // warning: suspicious lack of parentheses (rhs of ==>)
    B && C &&
  D
}

predicate Q8(A: bool, B: bool, C: bool, D: bool) {
  A
  ==>
    B && C &&
    D
}

predicate Q8a(A: bool, B: bool, C: bool, D: bool) {
  (A
  ==>
    B && C &&
    D
  ) &&
  (B || C)
}

predicate Q8b(A: bool, B: bool, C: bool, D: bool) {
    A &&
    B
  ==>
    B &&
    D
}

predicate Q8c(t: int, x: int, y: int)
{
  && (t == 2 ==> x < y)
  && (|| t == 3
      || t == 2
     ==>
     && x == 100
     && y == 1000
     )
  && (t == 4 ==> || 0 <= x || 0 <= y)
}

predicate Q8d(t: int, x: int, y: int)
{
  || t == 3
  || t == 2
  ==>
  && x == 100
  && y == 1000
}

predicate Q9(A: bool, B: bool, C: bool) {
  A ==> B ==>
  C
}

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
    Q(x) &&
    R(x)
}

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) && Q(x) ==>
    R(x)
}

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) ==>
    R(x)
}

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
    Q(x) ==>
    R(x)
}

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) ==>
  R(x)
}

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
  forall y :: Q(y) ==>
  R(x)
}

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: (P(x) ==> Q(x)) && // warning: suspicious lack of parentheses (forall)
  R(x)
}

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x ::
  (P(x) ==> Q(x)) &&
  R(x)
}

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x ::
    (P(x) ==> Q(x)) &&
    R(x)
}

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool) {
  exists x :: (P(x) ==> Q(x)) && // warning: suspicious lack of parentheses (exists)
  R(x)
}

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool) {
  exists x :: P(x) && // warning: suspicious lack of parentheses (exists)
  exists y :: Q(y) && // warning: suspicious lack of parentheses (exists)
  R(x)
}

lemma Injective()
  ensures forall x, y ::
    Negate(x) == Negate(y)
    ==> x == y
{
}

function Negate(x: int): int {
  -x
}

predicate Quant0(s: string) {
  && s != []
  && (|| 'a' <= s[0] <= 'z'
      || 'A' <= s[0] <= 'Z')
  && forall i :: 1 <= i < |s| ==>
    || 'a' <= s[i] <= 'z'
    || 'A' <= s[i] <= 'Z'
    || '0' <= s[i] <= '9'
}

predicate Quant1(m: array2<string>, P: int -> bool)
  reads m
{
  forall i :: 0 <= i < m.Length0 && P(i) ==> forall j :: 0 <= j < m.Length1 ==>
    m[i, j] != ""
}

predicate Quant2(s: string) {
  forall i :: 0 <= i < |s| ==> if s[i] == '*' then false else
    s[i] == 'a' || s[i] == 'b'
}

ghost predicate Quant3(f: int -> int, g: int -> int) {
  forall x ::
    f(x) == g(x)
}

ghost predicate Quant4(f: int -> int, g: int -> int) {
  forall x :: f(x) ==
    g(x)
}

ghost predicate Quant5(f: int -> int, g: int -> int) {
  forall x :: f(x)
     == g(x)
}

function If0(s: string): int {}

function If1(s: string): int {}

function If2(s: string): int {}

function If3(s: string): int {}

predicate Waterfall(A: bool, B: bool, C: bool, D: bool, E: bool) {
          A ==>
        B ==>
      C ==>
    D ==>
  E
}

ghost predicate MoreOps0(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) <== Q(x) <== // warning: suspicious lack of parentheses (rhs of <==)
    R(x)
}

ghost predicate MoreOps1(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) <== Q(x) <==>
    R(x)
}

ghost predicate MoreOps2(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) <==>
    R(x)
}

ghost predicate MoreOps3(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) <==>
    R(x) ==>
    P(x)
}

ghost predicate MoreOps4(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) <==> Q(x) && // warning: suspicious lack of parentheses (rhs of <==>)
    R(x)
}

lemma IntLemma(x: int)

function StmtExpr0(x: int): int {}

function StmtExpr1(x: int): int {}

function StmtExpr2(x: int): int {}

function StmtExpr3(x: int): int {}

function FunctionWithDefaultParameterValue(x: int, y: int := 100): int

function UseDefaultValues(x: int): int {}

function Square(x: int): int {
  x * x
}

predicate Let0(lo: int, hi: int)
  requires lo <= hi
{
  forall x :: lo <= x < hi ==> var square := Square(x);
    0 <= square
}

ghost predicate Let1(P: int -> bool) {
  forall x :: 0 <= x && P(x) ==> var bigger :| x <= bigger;
    0 <= bigger
}

predicate SomeProperty<X>(x: X)

method Parentheses0(arr: array<int>, P: int -> bool)
{}

method Parentheses1(w: bool, x: int)
{}

datatype Record = Record(x: int, y: int)

method Parentheses2(w: bool, x: int, y: int)
{}

method Parentheses3(w: bool, arr: array<int>, m: array2<int>, i: nat, j: nat)
  requires i < j < arr.Length <= m.Length0 <= m.Length1
{}

codatatype Stream = More(head: int, tail: Stream)

method Parentheses4(w: bool, s: Stream, t: Stream)
{}
/**** revisit the following when the original match'es are being resolved (https://github.com/dafny-lang/dafny/pull/2734)
datatype Color = Red | Blue

method Parentheses5(w: bool, color: Color) {}
***/

module MyModule {
  function MyFunction(x: int): int
  lemma Lemma(x: int)
}

module QualifiedNames {}  

module MatchAcrossMultipleLines {
  datatype PQ = P(int) | Q(bool)

  method M(s: set<PQ>)
    requires
      (forall pq | pq in s :: match pq {})
  {
  }

  datatype YZ = Y | Z

  function F(A: bool, B: int, C: YZ): int
    requires C != Y
  {}
}




// Tossed File 11:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_logic.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_logic.dfy
// num_methods: 0
// num_lemmas: 20
// num_classes: 0
// num_functions: 0
// num_predicates: 3
// num_ensures: 32
// num_requires: 9
// num_lines: 205
// num_no_ensures: 0
// num_no_requires: 10
// num_none_either: 4
// keepToss: TOSS
/* Review of logical connectives and properties of first-order logic. */

/* We'll be using boolean logic both to define protocols and to state their
 * properties, so it helps if you have an understanding of what the connectives
 * of logic mean and have a little fluency with manipulating them. */

/* The first section of "An Introduction to Abstract Mathematics" by Neil
 * Donaldson and Alessandra Pantano might be helpful:
 * https://www.math.uci.edu/~ndonalds/math13/notes.pdf
 */

/* The core of logic is the _proposition_. For us, a proposition like `2 < 3` is
 * going to be a boolean, with the interpretation that the proposition is true,
 * well, if the boolean is true, and false if not. That proposition is clearly
 * true.
 */

lemma ExampleProposition()
{
  assert 2 < 3;
}

/* Another example: `7 - 3 == 3` is clearly false, but it's still a
 * proposition.
 */
lemma SomethingFalse()
{}

/* On the other hand something like `7 * false < 8` isn't a
 * proposition at all since it has a type error - we won't have to worry too
 * much about these because Dafny will quickly and easily catch such mistakes.
 */
lemma SomethingNonsensical()
{}

/* In Dafny, we can write lemmas with arguments, which are logical variables (of
 * the appropriate types). From here on we'll shift to stating logical properties
 * as ensures clauses of lemmas, the typical way they'd be packaged in Dafny. */
lemma AdditionCommutes(n: int, m: int)
  ensures n + m == m + n
{}

/* Let's start by going over the simplest logical connectives: && ("and") and ||
 * ("or"). In these examples think of the input booleans as being arbitrary
 * predicates, except that by the time we've passed them to these lemmas their
 * represented as just a truth value. */

lemma ProveAndFromBoth(p1: bool, p2: bool)
  requires p1
  requires p2
  ensures p1 && p2
{}

lemma FromAndProveRight(p1: bool, p2: bool)
  requires p1 && p2
  ensures p2
{}

lemma ProveOrFromLeft(p1: bool, p2: bool)
  requires p1
  ensures p1 || p2
{}

/* Let's also see _negation_ written `!p`, boolean negation. Asserting or
 * ensuring `!p` is the way we prove it's false. */
lemma DoubleNegation(p: bool)
  requires p
  ensures !!p
{}

lemma LawOfExcludedMiddle(p: bool)
  ensures p || !p
{}

/* Now we'll introduce boolean implication, `p ==> q`, read as "if p, then q". In "p
 * ==> q" we'll sometimes refer to "p" as a hypothesis and "q" as a conclusion.
 * Here are some alternative English logical
 * statements and how they map to implication:
 *
 * "p if q" means "q ==> p"
 * "p only if q" means "p ==> q" (this one can be tricky!)
 * "p implies q" means "p ==> q"
 */

/* Note that p ==> q is itself a proposition! Here's its "truth table", showing
 * all possible combinations of p and q and whether p ==> q is true: */
lemma ImplicationTruthTable()
  ensures false ==> false
  ensures false ==> true
  ensures !(true ==> false)
  ensures false ==> true
{}

/* One of the most famous rules of logic, which allows us to take an implication
 * (already proven correct) and a proof of its hypothesis to derive its
 * conclusion.
 *
 * Note that both parts are important! We can prove `false ==> 2 < 1` but will
 * never be able to use ModusPonens on this to prove `2 < 1`. Well we could, but
 * since this is obviously false it would mean we accidentally assumed false
 * somewhere else - this is also called an _inconsistency_.
 */
lemma ModusPonens(p1: bool, p2: bool)
  requires p1 ==> p2
  requires p1
  ensures p2
{}

/* We can write a lemma above as implications in ensures clauses, rather than
 * using preconditions. The key difference is that calling `FromAndProveLeft(p1,
 * p2)` for example will cause Dafny to immediately prove `p1 && p2`, whereas we
 * can always call `AndProvesBoth(p1, p2)` and Dafny won't check anything
 * (because the implications are true regardless of p1 and p2). */
lemma AndProvesBoth(p1: bool, p2: bool)
  ensures p1 && p2 ==> p1
  ensures p1 && p2 ==> p2
{}

/* Let's introduce one more logical connective: `p <==> q`, "p if and only if q"
 * (also written "iff" and pronounced "if and only if"). This has the same truth
 * value as `p == q`. The whole thing is sometimes called a "biconditional".
 * This rule is a little like modus ponens but requiring the implication is
 * stronger than needed. */
lemma ProveFromBiconditional(p1: bool, p2: bool)
  requires p1
  requires p1 <==> p2
  ensures p2
{}

/* Simplifying and comprehending logical expressions is something you'll
 * gradually get practice with. It can get quite complicated! */
lemma SomeEquivalences(p1: bool, p2: bool)
  ensures ((p1 ==> p2) && p1) ==> p2
  // !p2 ==> !p1 is called the "contrapositive" of p1 ==> p2. It has the same
  // truth value.
  ensures (p1 ==> p2) <==> (!p2 ==> !p1)
  ensures !(p1 ==> !p2) <==> p1 && p2
  ensures ((p1 ==> p2) && (!p1 ==> p2)) <==> p2
  // you might want to think about this one:
  ensures (!p1 || (p1 ==> p2)) <==> (p1 ==> p2)
{}

lemma SomeMoreEquivalences(p1: bool, p2: bool, p3: bool)
  // note on parsing: <==> has the lowest priority, so all of these statements are
  // equivalences at the top level
  ensures (p1 && p2) && p3 <==> p1 && p2 && p3
  // this is what chained implications mean
  ensures p1 ==> p2 ==> p3 <==> p1 && p2 ==> p3
  ensures p1 ==> (p2 ==> p3) <==> p1 && p2 ==> p3
{}

/* Quantifiers */

/* To express and state more interesting properties, we'll need quantifiers -
 * that is, forall and exists. Dafny supports these as a way to write
 * propositions, and they produce a boolean value just like the other logical
 * connectives. */

lemma AdditionCommutesAsForall()
{}

/* In order to illustrate some properties of forall, we'll introduce some
 * arbitrary _predicates_ over integers to put in our examples. By not putting a
 * body we tell Dafny to define these terms, but not to assume anything about their
 * values except that they are deterministic. */
predicate P(x: int)
predicate Q(x: int)
// This is a predicate over two integers, often called a relation. You might
// also hear propositions, predicates, and predicates over multiple values all
// called relations - propositions are just 0-arity and predicates are 1-arity.
predicate R(x: int, y: int)

/* One operation you'll eventually want some fluency in is the ability to negate
 * logical expressions. Let's go through the rules. */
lemma SimplifyingNegations(p: bool, q: bool)
  ensures !(p && q) <==> !p || !q
  ensures !(p || q) <==> !p && !q
  ensures !(p ==> q) <==> p && !q
  ensures !!p <==> p
  ensures !(forall x :: P(x)) <==> (exists x :: !P(x))
  ensures !(exists x :: P(x)) <==> (forall x :: !P(x))
{}

/* Dafny supports a "where" clause in a forall. It's a shorthand for implication. */
lemma WhereIsJustImplies()
  // we need parentheses around each side for this to have the desired meaning
  ensures (forall x | P(x) :: Q(x)) <==> (forall x :: P(x) ==> Q(x))
{}

lemma NotForallWhere()
  ensures !(forall x | P(x) :: Q(x)) <==> exists x :: P(x) && !Q(x)
{}

/* Dafny also supports a "where" clause in an exists, as a shorthand for &&. */
lemma ExistsWhereIsJustAnd()
  // we need parentheses around each side for this to have the desired meaning
  ensures (exists x | P(x) :: Q(x)) <==> (exists x :: P(x) && Q(x))
  // Why this choice? It's so that the following property holds. Notice that for
  // all the negation rules we reverse && and ||, and exists and forall; this
  // preserves that _duality_ (a formal and pervasive concept in math and
  // logic).
  ensures !(forall x | P(x) :: Q(x)) <==> (exists x | P(x) :: !Q(x))
{}




// Tossed File 12:
// filename: dafny-sandbox_tmp_tmp3tu2bu8a_Stlc.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-sandbox_tmp_tmp3tu2bu8a_Stlc.dfy
// num_methods: 0
// num_lemmas: 12
// num_classes: 0
// num_functions: 6
// num_predicates: 5
// num_ensures: 12
// num_requires: 13
// num_lines: 261
// num_no_ensures: 0
// num_no_requires: 4
// num_none_either: 6
// keepToss: TOSS
﻿// Proving type safety of a Simply Typed Lambda-Calculus in Dafny
// adapted from Coq (http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html)

/// Utilities

// ... handy for partial functions
datatype option<A> = None | Some(get: A)

/// -----
/// Model
/// -----

/// Syntax

// Types
datatype ty =  TBase                             // (opaque base type)
            |  TArrow(T1: ty, T2: ty)            // T1 => T2
/*BOOL?
            | TBool                              // (base type for booleans)
?BOOL*/
/*NAT?
            |  TNat                              // (base type for naturals)
?NAT*/
/*REC?
            | TVar(id: int) | TRec(X: nat, T: ty)// (iso-recursive types)
?REC*/

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)
/*BOOL?
            | ttrue | tfalse                     // true, false        (boolean values)
            | tif(c: tm, a: tm, b: tm)           // if t then t else t (if expression)
?BOOL*/
/*NAT?
            | tzero | tsucc(p: tm) | tprev(n: tm)//                    (naturals)
/*BOOL?
            | teq(n1: tm, n2: tm)                //                    (equality on naturals)
?BOOL*/
?NAT*/
/*REC?
            | tfold(Tf: ty, tf: tm) | tunfold(tu: tm)//                (iso-recursive terms)
?REC*/

/// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tabs?
/*BOOL?
  || t.ttrue? || t.tfalse?
?BOOL*/
/*NAT?
  || peano(t)
?NAT*/
/*REC?
  || (t.tfold? && value(t.tf))
?REC*/
}

/*NAT?
predicate peano(t: tm)
{
  t.tzero? || (t.tsucc? && peano(t.p))
}
?NAT*/

// Free Variables and Substitution

function fv(t: tm): set<int> //of free variables of t
{}

function subst(x: int, s: tm, t: tm): tm //[x -> s]t
{}

/*REC?
function ty_fv(T: ty): set<int> //of free type variables of T
{}

function tsubst(X: int, S: ty, T: ty): ty
{}

predicate ty_closed(T: ty)
{
  forall x :: x !in ty_fv(T)
}
?REC*/

// Reduction
function step(t: tm): option<tm>
{}

// Multistep reduction:
// The term t reduces to the term t' in n or less number of steps.
predicate reduces_to(t: tm, t': tm, n: nat)
  decreases n;
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

// Examples
lemma lemma_step_example1(n: nat)
  requires n > 0;
  // (\x:B=>B.x) (\x:B.x) reduces to (\x:B.x)
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
}


/// Typing

// A context is a partial map from variable names to types.
function find(c: map<int,ty>, x: int): option<ty>
{}
function extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x:=T]
}

// Typing Relation
function has_type(c: map<int,ty>, t: tm): option<ty>
  decreases t;
{}

// Examples

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
}

lemma example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{}

lemma nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
{}

lemma nonexample_typing_3(S: ty, T: ty)
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{}

/*BOOL?
lemma example_typing_bool()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))))) ==
          Some(TArrow(TBase, TArrow(TBase, TArrow(TBool, TBase))));
{}
?BOOL*/

/*NAT?
lemma example_typing_nat()
  ensures has_type(map[], tabs(0, TNat, tprev(tvar(0)))) == Some(TArrow(TNat, TNat));
{}
?NAT*/

/*REC?
// TODO
lemma example_typing_rec()
  // ∅ |- foldµT. T→α(λx : µT. T → α. (unfold x) x) : µT. T → α
  ensures has_type(map[], tfold(TRec(0, TArrow(TVar(0), TBase)), tabs(0, TRec(0, TArrow(TVar(0), TBase)), tapp(tunfold(tvar(0)), tvar(0))))) ==
          Some(TRec(0, TArrow(TVar(0), TBase)));
{}
?REC*/

/// -----------------------
/// Type-Safety Properties
/// -----------------------

// Progress:
// A well-typed term is either a value or it can step.
lemma theorem_progress(t: tm)
  requires has_type(map[], t).Some?;
  ensures value(t) || step(t).Some?;
{
}

// Towards preservation and the substitution lemma

// If x is free in t and t is well-typed in some context,
// then this context must contain x.
lemma {:induction c, t} lemma_free_in_context(c: map<int,ty>, x: int, t: tm)
  requires x in fv(t);
  requires has_type(c, t).Some?;
  ensures find(c, x).Some?;
  decreases t;
{
}

// A closed term does not contain any free variables.
// N.B. We're only interested in proving type soundness of closed terms.
predicate closed(t: tm)
{
  forall x :: x !in fv(t)
}

// If a term can be well-typed in an empty context,
// then it is closed.
lemma corollary_typable_empty__closed(t: tm)
  requires has_type(map[], t).Some?;
  ensures closed(t);
{}

// If a term t is well-typed in context c,
//    and context c' agrees with c on all free variables of t,
// then the term t is well-typed in context c',
//      with the same type as in context c.
lemma {:induction t} lemma_context_invariance(c: map<int,ty>, c': map<int,ty>, t: tm)
  requires has_type(c, t).Some?;
  requires forall x: int :: x in fv(t) ==> find(c, x) == find(c', x);
  ensures has_type(c, t) == has_type(c', t);
  decreases t;
{}

// Substitution preserves typing:
// If  s has type S in an empty context,
// and t has type T in a context extended with x having type S,
// then [x -> s]t has type T as well.
lemma lemma_substitution_preserves_typing(c: map<int,ty>, x: int, s: tm, t: tm)
  requires has_type(map[], s).Some?;
  requires has_type(extend(x, has_type(map[], s).get, c), t).Some?;
  ensures has_type(c, subst(x, s, t)) == has_type(extend(x, has_type(map[], s).get, c), t);
  decreases t;
{}


// Preservation:
// A well-type term which steps preserves its type.
lemma theorem_preservation(t: tm)
  requires has_type(map[], t).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get) == has_type(map[], t);
{}

// A normal form cannot step.
predicate normal_form(t: tm)
{
  step(t).None?
}

// A stuck term is a normal form that is not a value.
predicate stuck(t: tm)
{
  normal_form(t) && !value(t)
}

// Type soundness:
// A well-typed term cannot be stuck.
lemma corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t) == Some(T);
  requires reduces_to(t, t', n);
  ensures !stuck(t');
  decreases n;
{}

/// QED



// Tossed File 13:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_Streams.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny3_Streams.dfy
// num_methods: 0
// num_lemmas: 21
// num_classes: 0
// num_functions: 11
// num_predicates: 1
// num_ensures: 20
// num_requires: 3
// num_lines: 165
// num_no_ensures: 2
// num_no_requires: 19
// num_none_either: 10
// keepToss: TOSS
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function append(M: Stream, N: Stream): Stream
{}

// ----- f, g, and maps

type X

ghost function f(x: X): X
ghost function g(x: X): X

ghost function map_f(M: Stream<X>): Stream<X>
{}

ghost function map_g(M: Stream<X>): Stream<X>
{}

ghost function map_fg(M: Stream<X>): Stream<X>
{}

// ----- Theorems

// map (f * g) M = map f (map g M)
greatest lemma Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{}
greatest lemma Theorem0_Alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{}
lemma Theorem0_Par(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{}
lemma Theorem0_Ind(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{}
lemma Theorem0_AutoInd(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
}

// map f (append M N) = append (map f M) (map f N)
greatest lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{}
greatest lemma Theorem1_Alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{}
lemma Theorem1_Par(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{}
lemma Theorem1_Ind(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{}
lemma Theorem1_AutoInd(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
}
lemma Theorem1_AutoForall()
{}

// append NIL M = M
lemma Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M;
{
  // trivial
}

// append M NIL = M
greatest lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M;
{}
greatest lemma Theorem3_Alt(M: Stream<X>)
  ensures append(M, Nil) == M;
{}

// append M (append N P) = append (append M N) P
greatest lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{}
greatest lemma Theorem4_Alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{}

// ----- Flatten

// Flatten can't be written as just:
//
//     function SimpleFlatten(M: Stream<Stream>): Stream
//     {}
//
// because this function fails to be productive given an infinite stream of Nil's.
// Instead, here are two variations of SimpleFlatten.  The first variation (FlattenStartMarker)
// prepends a "startMarker" to each of the streams in "M".  The other (FlattenNonEmpties)
// insists that "M" contain no empty streams.  One can prove a theorem that relates these
// two versions.

// This first variation of Flatten returns a stream of the streams in M, each preceded with
// "startMarker".

ghost function FlattenStartMarker<T>(M: Stream<Stream>, startMarker: T): Stream
{}

ghost function PrependThenFlattenStartMarker<T>(prefix: Stream, M: Stream<Stream>, startMarker: T): Stream
{}

// The next variation of Flatten requires M to contain no empty streams.

greatest predicate StreamOfNonEmpties(M: Stream<Stream>)
{
  match M
  case Nil => true
  case Cons(s, N) => s.Cons? && StreamOfNonEmpties(N)
}

ghost function FlattenNonEmpties(M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{}

ghost function PrependThenFlattenNonEmpties(prefix: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{}

// We can prove a theorem that links the previous two variations of flatten.  To
// do that, we first define a function that prepends an element to each stream
// of a given stream of streams.

ghost function Prepend<T>(x: T, M: Stream<Stream>): Stream<Stream>
{}

greatest lemma Prepend_Lemma<T>(x: T, M: Stream<Stream>)
  ensures StreamOfNonEmpties(Prepend(x, M));
{}

lemma Theorem_Flatten<T>(M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    FlattenStartMarker(M, startMarker) == FlattenNonEmpties(Prepend(startMarker, M));
{}

greatest lemma Lemma_Flatten<T>(prefix: Stream, M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    PrependThenFlattenStartMarker(prefix, M, startMarker) == PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M));
{}

greatest lemma Lemma_FlattenAppend0<T>(s: Stream, M: Stream<Stream>, startMarker: T)
  ensures PrependThenFlattenStartMarker(s, M, startMarker) == append(s, PrependThenFlattenStartMarker(Nil, M, startMarker));
{}

greatest lemma Lemma_FlattenAppend1<T>(s: Stream, M: Stream<Stream>)
  requires StreamOfNonEmpties(M);
  ensures PrependThenFlattenNonEmpties(s, M) == append(s, PrependThenFlattenNonEmpties(Nil, M));
{}




// Tossed File 14:
// filename: AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary.dfy
// num_methods: 3
// num_lemmas: 12
// num_classes: 0
// num_functions: 5
// num_predicates: 2
// num_ensures: 15
// num_requires: 8
// num_lines: 114
// num_no_ensures: 1
// num_no_requires: 8
// num_none_either: 5
// keepToss: TOSS
// Noa Leron 207131871
// Tsuri Farhana 315016907


// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
datatype Unary = Zero | Suc(pred: Unary)

ghost function UnaryToNat(x: Unary): nat {}

ghost function NatToUnary(n: nat): Unary {}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}

function Add(x: Unary, y: Unary): Unary {}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{}

function Mul(x: Unary, y: Unary): Unary {}

lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Sub(x, y) < x
{
}

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
{
}

/*
Goal: implement correcly and clearly, using iterative code (no recursion), documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal

- DO NOT modify the specification or any of the definitions given in this file
- Not all definitions above are relevant, some are simply included as examples
- Feel free to use existing non-ghost functions/predicates in your code, and existing lemmas (for the proof) in your annotations
- New functions/predicates may be added ONLY as ghost
- If it helps you in any way, a recursive implementation + proof can be found in the book and the downloadable source file
  [https://program-proofs.com/code.html example code in Dafny, source file 7-Unary.dfy]
*/

method{:verify false} IterativeDivMod'(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{}

method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{}

lemma AddMulEqMulSuc(a: Unary, b: Unary)
  ensures Mul(Suc(a), b) == Add(Mul(a, b), b)
{}

lemma AddMulSucSubEqAddMul(d: Unary, y: Unary, x0: Unary)
  requires !Less(x0, y)
  requires y != Zero
  ensures Add(Mul(Suc(d), y), Sub(x0, y)) == Add(Mul(d, y), x0)
{}

lemma AddTransitive(a: Unary, b: Unary, c: Unary)
  ensures Add(a, Add(b, c)) == Add(Add(a, b), c)
{}

lemma AddCommutative(a: Unary, b: Unary)
  ensures Add(a, b) == Add(b, a)
{}



method Main() {}



// Tossed File 15:
// filename: Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Helper.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Helper.dfy
// num_methods: 0
// num_lemmas: 20
// num_classes: 0
// num_functions: 3
// num_predicates: 0
// num_ensures: 24
// num_requires: 30
// num_lines: 139
// num_no_ensures: 1
// num_no_requires: 4
// num_none_either: 1
// keepToss: TOSS
/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {}

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {}

  lemma Log2FloorDef(n: nat)
    requires n >= 1
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
  {}

  function boolToNat(b: bool): nat {}

  /*******
   Lemmas
  *******/

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    requires x == y
    ensures f(x) == f(y)
  {}

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    requires a == b
    requires x != 0.0
    ensures a / x == b / x
  {}

  lemma DivModAddDenominator(n: nat, m: nat)
    requires m > 0
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
  {}

  lemma DivModIsUnique(n: int, m: int, a: int, b: int)
    requires n >= 0
    requires m > 0
    requires 0 <= b < m
    requires n == a * m + b
    ensures a == n / m
    ensures b == n % m
  {}

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    requires a > 0
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
  {}

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {}

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 1
    ensures Power(base, exponent) >= 1
  {}

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
  {}

  lemma NLtPower2Log2FloorOf2N(n: nat)
    requires n >= 1
    ensures n < Power(2, Log2Floor(2 * n))
  {}

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    ensures a * b <= c * d
  {}

  lemma MulMonotonicStrictRhs(b: nat, c: nat, d: nat)
    requires b < d
    requires c > 0
    ensures c * b < c * d
  {}

  lemma MulMonotonicStrict(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    requires (a != c && d > 0) || (b != d && c > 0)
    ensures a * b < c * d
  {}

  lemma AdditionOfFractions(x: real, y: real, z: real)
    requires z != 0.0
    ensures (x / z) + (y / z) == (x + y) / z
  {}

  lemma DivSubstituteDividend(x: real, y: real, z: real)
    requires y != 0.0
    requires x == z
    ensures x / y == z / y
  {}

  lemma DivSubstituteDivisor(x: real, y: real, z: real)
    requires y != 0.0
    requires y == z
    ensures x / y == x / z
  {}

  lemma DivDivToDivMul(x: real, y: real, z: real)
    requires y != 0.0
    requires z != 0.0
    ensures (x / y) / z == x / (y * z)
  {}

  lemma NatMulNatToReal(x: nat, y: nat)
    ensures (x * y) as real == (x as real) * (y as real)
  {}

  lemma SimplifyFractions(x: real, y: real, z: real)
    requires z != 0.0
    requires y != 0.0
    ensures (x / z) / (y / z) == x / y
  {}

  lemma PowerOfTwoLemma(k: nat)
    ensures (1.0 / Power(2, k) as real) / 2.0 == 1.0 / (Power(2, k + 1) as real)
  {}
}




