// Kept File 1:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_MatrixFun_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_MatrixFun_no_hints.dfy
// keepToss: KEEP
// reasoning: These specifications involve non-trivial 2D array manipulations (horizontal mirroring and matrix transposition) that require careful index management and understanding of array bounds, making them good tests for implementation skills.

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method MirrorImage<T>(m: array2<T>)
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==>
            m[i,j] == old(m[i, m.Length1-1-j])
{}

method Flip<T>(m: array2<T>)
  requires m.Length0 == m.Length1
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == old(m[j,i])
{}

method Main()
{}

method PrintMatrix<T>(m: array2<T>)
{}


// Kept File 2:
// filename: dafny-synthesis_task_id_760_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_760_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification requires implementing logic to check if all elements in an array are identical, involving quantified reasoning over array indices and understanding the relationship between universal and existential quantifiers in the postconditions.

method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
{}
// Kept File 3:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_MajorityVote_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_MajorityVote_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification implements the Boyer-Moore majority vote algorithm, which is a non-trivial problem requiring careful reasoning about loop invariants, ghost parameters, and mathematical properties of majority elements in sequences.

// RUN: %testDafnyForEachResolver "%s"


// Rustan Leino, June 2012.
// This file verifies an algorithm, due to Boyer and Moore, that finds the majority choice
// among a sequence of votes, see http://www.cs.utexas.edu/~moore/best-ideas/mjrty/.
// Actually, this algorithm is a slight variation on theirs, but the general idea for why
// it is correct is the same.  In the Boyer and Moore algorithm, the loop counter is advanced
// by exactly 1 each iteration, which means that there may or may not be a "current leader".
// In my program below, I had instead written the loop invariant to say there is always a
// "current leader", which requires the loop index sometimes to skip a value.
//
// This file has two versions of the algorithm.  In the first version, the given sequence
// of votes is assumed to have a (strict) majority choice, meaning that strictly more than
// 50% of the votes are for one candidate.  It is convenient to have a name for the majority
// choice, in order to talk about it in specifications.  The easiest way to do this in
// Dafny is probably to introduce a ghost parameter with the given properties.  That's what
// the algorithm does, see parameter K.  The postcondition is thus to output the value of
// K, which is done in the non-ghost out-parameter k.
// The proof of the algorithm requires two lemmas.  These lemmas are proved automatically
// by Dafny's induction tactic.
//
// In the second version of the program, the main method does not assume there is a majority
// choice.  Rather, it eseentially uses the first algorithm and then checks if what it
// returns really is a majority choice.  To do this, the specification of the first algorithm
// needs to be changed slightly to accommodate the possibility that there is no majority
// choice.  That change in specification is also reflected in the loop invariant.  Moreover,
// the algorithm itself now needs to extra 'if' statements to see if the entire sequence
// has been searched through.  (This extra 'if' is essentially already handled by Boyer and
// Moore's algorithm, because it increments the loop index by 1 each iteration and therefore
// already has a special case for the case of running out of sequence elements without a
// current leader.)
// The calling harness, DetermineElection, somewhat existentially comes up with the majority
// choice, if there is such a choice, and then passes in that choice as the ghost parameter K
// to the main algorithm.  Neat, huh?

// Language comment:
// The "(==)" that sits after some type parameters in this program says that the actual
// type argument must support equality.

// Advanced remark:
// There is a subtle situation in the verification of DetermineElection.  Suppose the type
// parameter Candidate denotes some type whose instances depend on which object are
// allocated.  For example, if Candidate is some class type, then more candidates can come
// into being by object allocations (using "new").  What does the quantification of
// candidates "c" in the postcondition of DetermineElection now mean--all candidates that
// existed in the pre-state or (the possibly larger set of) all candidates that exist in the
// post-state?  (It means the latter.)  And if there does not exist a candidate in majority
// in the pre-state, could there be a (newly created) candidate in majority in the post-state?
// This will require some proof.  The simplest argument seems to be that even if more candidates
// are created during the course of DetermineElection, such candidates cannot possibly
// be in majority in the sequence "a", since "a" can only contain candidates that were already
// created in the pre-state.  This property is easily specified by adding a postcondition
// to the Count function.  Alternatively, one could have added the antecedent "c in a" or
// "old(allocated(c))" to the "forall c" quantification in the postcondition of DetermineElection.

// About reading the proofs:
// Dafny proves the FindWinner algorithm from the given loop invariants and the two lemmas
// Lemma_Unique and Lemma_Split.  In showing this proof to some colleagues, they found they
// were not as quick as Dafny in constructing the proof from these ingredients.  For a human
// to understand the situation better, it helps to take smaller (and more) steps in the proof.
// At the end of this file, Nadia Polikarpova has written two versions of FindWinner that does
// that, using Dafny's support for calculational proofs.

function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{}

ghost predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{}

// Here is the first version of the algorithm, the one that assumes there is a majority choice.

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{}

// ------------------------------------------------------------------------------

// Here is the second version of the program, the one that also computes whether or not
// there is a majority choice.

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
{}

// The difference between SearchForWinner for FindWinner above are the occurrences of the
// antecedent "hasWinner ==>" and the two checks for no-more-votes that may result in a "return"
// statement.

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|  // K has a (strict) majority of the votes
  ensures hasWinner ==> k == K  // find K
{}

// ------------------------------------------------------------------------------

// Here are two lemmas about Count that are used in the methods above.

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{}

// ------------------------------------------------------------------------------

// This version uses more calculations with integer formulas
method FindWinner'<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{}

// This version uses more calculations with boolean formulas
method FindWinner''<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)  // K has a (strict) majority of the votes
  ensures k == K  // find K
{}


// Kept File 4:
// filename: Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock_no_hints.dfy
// keepToss: KEEP
// reasoning: This is a classic algorithmic problem requiring non-trivial optimization to find maximum profit from stock prices, with meaningful constraints and a postcondition that captures the correctness requirement.

method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{}


// Kept File 5:
// filename: dafny-synthesis_task_id_18_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_18_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification requires understanding set membership, string manipulation, and maintaining character order while filtering, which is non-trivial and tests important algorithmic reasoning skills.

method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{}
// Kept File 6:
// filename: Clover_two_sum_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_two_sum_no_hints.dfy
// keepToss: KEEP
// reasoning: This is a well-specified two-sum problem that requires implementing an efficient algorithm with non-trivial loop invariants and careful indexing logic to find the lexicographically first valid pair.

method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{}

// Kept File 7:
// filename: Software-Verification_tmp_tmpv4ueky2d_Valid Palindrome_valid_panlindrome_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Valid Palindrome_valid_panlindrome_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires implementing a palindrome checker with a non-trivial postcondition that involves quantified reasoning over array indices, testing understanding of array bounds and symmetric comparison logic.

method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{}


// Kept File 8:
// filename: Clover_reverse_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_reverse_no_hints.dfy
// keepToss: KEEP
// reasoning: Classic array reversal with proper specification using old() and quantified postcondition, requires understanding of array manipulation and index arithmetic.

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

// Kept File 9:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-2-MaxTree-class_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-2-MaxTree-class_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires implementing a complex tree traversal algorithm with sophisticated invariant reasoning about ghost fields, representation sets, and proving both upper bound and existence properties for the maximum value.

// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 2: Maximum in a tree
http://foveoos2011.cost-ic0701.org/verification-competition

Given: A non-empty binary tree, where every node carries an integer.

Implement and verify a program that computes the maximum of the values
in the tree.

Please base your program on the following data structure signature:

public class Tree {}

You may represent empty trees as null references or as you consider
appropriate.
*/

// Remarks:

// The specification of this program uses the common dynamic-frames idiom in Dafny:  the
// ghost field 'Contents' stores the abstract value of an object, the ghost field 'Repr'
// stores the set of (references to) objects that make up the representation of the object
// (which in this case is the Tree itself plus the 'Repr' sets of the left and right
// subtrees), and a function 'Valid()' that returns 'true' when an object is in a
// consistent state (that is, when an object satisfies the "class invariant").

// The design I used was to represent an empty tree as a Tree object whose left and
// right pointers point to the object iself.  This is convenient, because it lets
// clients of Tree and the implementation of Tree always use non-null pointers to
// Tree objects.

// What needs to be human-trusted about this program is that the 'requires' and
// 'ensures' clauses (that is, the pre- and postconditions, respectively) of
// 'ComputeMax' are correct.  And, since the specification talks about the ghost
// variable 'Contents', one also needs to trust that the 'Valid()' function
// constrains 'Contents' in a way that a human thinks matches the intuitive
// definition of what the contents of a tree is.

// To give a taste of that the 'Valid()' function does not over-constrain the
// object, I have included two instance constructors, 'Empty()' and 'Node(...)'.
// To take this a step further, one could also write a 'Main' method that
// builds somme tree and then calls 'ComputeMax', but I didn't do that here.

// About Dafny:
// As always (when it is successful), Dafny verifies that the program does not
// cause any run-time errors (like array index bounds errors), that the program
// terminates, that expressions and functions are well defined, and that all
// specifications are satisfied.  The language prevents type errors by being type
// safe, prevents dangling pointers by not having an "address-of" or "deallocate"
// operation (which is accommodated at run time by a garbage collector), and
// prevents arithmetic overflow errors by using mathematical integers (which
// is accommodated at run time by using BigNum's).  By proving that programs
// terminate, Dafny proves that a program's time usage is finite, which implies
// that the program's space usage is finite too.  However, executing the
// program may fall short of your hopes if you don't have enough time or
// space; that is, the program may run out of space or may fail to terminate in
// your lifetime, because Dafny does not prove that the time or space needed by
// the program matches your execution environment.  The only input fed to
// the Dafny verifier/compiler is the program text below; Dafny then automatically
// verifies and compiles the program (for this program in less than 2.5 seconds)
// without further human intervention.

class Tree {
  // an empty tree is represented by a Tree object with left==this==right
  var value: int
  var left: Tree?
  var right: Tree?

  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {}

  function IsEmpty(): bool
    requires Valid();
    reads this, Repr;
    ensures IsEmpty() <==> Contents == [];
  {}

  constructor Empty()
    ensures Valid() && Contents == [];
  {}

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid();
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents;
  {}

  lemma exists_intro<T>(P: T ~> bool, x: T)
    requires P.requires(x)
    requires P(x)
    ensures exists y :: P.requires(y) && P(y)
  {
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty();
    ensures forall x :: x in Contents ==> x <= mx;
    ensures exists x :: x in Contents && x == mx;
  {}
}


// Kept File 10:
// filename: dafny-synthesis_task_id_741_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_741_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification requires understanding string indexing, quantifiers (forall/exists), and logical reasoning about when all characters are the same versus when they differ, making it a meaningful test of implementation skills.

method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{}
// Kept File 11:
// filename: dafny-synthesis_task_id_273_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_273_no_hints.dfy
// keepToss: KEEP
// reasoning: Clear specification requiring element-wise subtraction of two sequences with proper indexing and length constraints.

method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{}
// Kept File 12:
// filename: Dafny_Programs_tmp_tmp99966ew4_lemma_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Programs_tmp_tmp99966ew4_lemma_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification involves a non-trivial search algorithm with complex preconditions about array relationships, requiring sophisticated reasoning about loop invariants and the interplay between the lemma and main method.

lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{}
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{}


// Kept File 13:
// filename: dafny-synthesis_task_id_95_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_95_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires finding the minimum length among nested sequences, which involves non-trivial iteration logic and understanding of quantified expressions with both universal and existential constraints.

method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{}
// Kept File 14:
// filename: dafny-synthesis_task_id_776_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_776_no_hints.dfy
// keepToss: KEEP
// reasoning: The specification requires implementing both a vowel predicate and a method that counts characters with vowel neighbors on both sides, involving set comprehension and index bounds reasoning.

predicate IsVowel(c: char)
{}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{}
// Kept File 15:
// filename: Clover_even_list_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_even_list_no_hints.dfy
// keepToss: KEEP
// reasoning: This specification requires implementing array filtering with order preservation, involving complex postconditions about element membership, evenness properties, and maintaining relative ordering from the original array.

method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{}

// Tossed File 1:
// filename: Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Helper_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Helper_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a module of helper lemmas and basic mathematical utilities rather than a meaningful programming problem that tests implementation skills.
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




// Tossed File 2:
// filename: DafnyPrograms_tmp_tmp74_f9k_c_invertarray_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/DafnyPrograms_tmp_tmp74_f9k_c_invertarray_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a trivial array reversal problem that requires only a simple loop with index swapping - too basic to meaningfully test specification understanding or algorithmic reasoning.
/**
  Inverts an array of ints.
 */
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{}



// Tossed File 3:
// filename: dafny-synthesis_task_id_401_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_401_no_hints.dfy
// keepToss: TOSS
// reasoning: The postcondition contains a contradiction: it requires result[i] == a[i] while also requiring result[i][j] == a[i][j] + b[i][j], which would only be satisfied if all elements of b are zero.
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{}


// Tossed File 4:
// filename: Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_ExtensibleArray_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_ExtensibleArray_no_hints.dfy
// keepToss: TOSS
// reasoning: This specification only declares method signatures and predicates without any implementation bodies or meaningful constraints - the ghost predicate Valid() and all methods have empty bodies, making it trivial to implement (just return arbitrary values or do nothing).
class ExtensibleArray<T(0)> {
  // abstract state
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  //concrete state
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int   // number of elements
  var M: int   // number of elements in depot

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {}

  constructor ()
    ensures Valid() && fresh(Repr) && Elements == []
  {}

  function Get(i: int): T
    requires Valid() && 0 <= i < |Elements|
    ensures Get(i) == Elements[i]
    reads Repr
  {}

  method Set(i: int, t: T)
    requires Valid() && 0 <= i < |Elements|
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements)[i := t]
{}

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Elements == old(Elements) + [t]
  {}
  
}



// Tossed File 5:
// filename: Dafny-demo_tmp_tmpkgr_dvdi_Dafny_BinarySearch_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-demo_tmp_tmpkgr_dvdi_Dafny_BinarySearch_no_hints.dfy
// keepToss: TOSS
// reasoning: The sorted predicate is empty (missing implementation), making the specification incomplete and unusable without first defining what "sorted" means.

predicate sorted(a: array?<int>, l: int, u: int)
	reads a
	requires a != null
	{}

method BinarySearch(a: array?<int>, key: int)
	returns (index: int)
	requires a != null && sorted(a,0,a.Length-1);
	ensures index >= 0 ==> index < a.Length && a[index] == key;
	ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
{}



// Tossed File 6:
// filename: DafnyProjects_tmp_tmp2acw_s4s_Power_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/DafnyProjects_tmp_tmp2acw_s4s_Power_no_hints.dfy
// keepToss: TOSS
// reasoning: The specification lacks the actual definition of the power function and has empty method bodies, making it impossible to verify correctness or test implementation ability without fundamental changes to the specification itself.
/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {}

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma {:induction a} productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ }


// A few test cases (checked statically by Dafny).
method testPowerDC() {}



// Tossed File 7:
// filename: dafny-synthesis_task_id_554_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_554_no_hints.dfy
// keepToss: TOSS
// reasoning: This specification is too simple - it only requires basic array traversal and filtering based on a trivial predicate (modulo operation), which doesn't meaningfully test advanced reasoning or algorithmic skills.
/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{}


// Tossed File 8:
// filename: Clover_min_array_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_min_array_no_hints.dfy
// keepToss: TOSS
// reasoning: This is a trivial array minimum problem that can be solved with a simple loop - too basic to meaningfully test implementation skills.
method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
{}



// Tossed File 9:
// filename: dafny-synthesis_task_id_2_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_2_no_hints.dfy
// keepToss: TOSS
// reasoning: The InArray predicate is missing its body definition, making the specification incomplete and unusable without additional implementation details.
predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}


// Tossed File 10:
// filename: SiLemma_tmp_tmpfxtryv2w_utils_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/SiLemma_tmp_tmpfxtryv2w_utils_no_hints.dfy
// keepToss: TOSS
// reasoning: These are all basic set theory lemmas with straightforward proofs that don't require complex algorithmic reasoning or program verification skills.
module Utils {

    lemma AllBelowBoundSize(bound: nat)
        ensures
            var below := set n : nat | n < bound :: n;
            |below| ==  bound
    {}

    lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
        requires forall n: nat :: n in a ==> n in b
        ensures |a| <= |b|
    {}

    lemma BoundedSetSize(bound: nat, values: set<nat>)
        requires forall n :: n in values ==> n < bound
        ensures |values| <= bound
    {}

    lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
        requires forall n: T, m: T :: m != n ==> f(n) != f(m)
        requires t == set n | n in s :: f(n)
        ensures |s| == |t|
    {}

    lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
        requires c == a + b
        requires forall t: T :: t in a ==> t !in b
        requires forall t: T :: t in b ==> t !in a
        ensures |c| == |a| + |b|
    {
    }

}



// Tossed File 11:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices_no_hints.dfy
// keepToss: TOSS
// reasoning: The specification is too simple - it only requires basic array manipulation and sequence concatenation understanding without complex logic, algorithms, or reasoning about data structures.
// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test was contributed by Bryan. It has shown some instabilities in the past.

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{}




// Tossed File 12:
// filename: HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Binary Search_binary_search_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Binary Search_binary_search_no_hints.dfy
// keepToss: TOSS
// reasoning: The helper predicates (sorted, distinct, not_found, found) are empty and lack bodies, making the specification incomplete and unusable without significant modification.
// Dafny verification of binary search alogirthm from binary_search.py
// Inspired by: https://ece.uwaterloo.ca/~agurfink/stqam/rise4fun-Dafny/#h211

method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{}

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{}

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
    reads arr
{}

// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{}

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{}






// Tossed File 13:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_BubbleSort_sol_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_BubbleSort_sol_no_hints.dfy
// keepToss: TOSS
// reasoning: The predicates are empty (no body provided) making it impossible to implement the sorting algorithm without knowing what "sorted" means, and bubble sort is a trivial textbook algorithm that doesn't meaningfully test specification understanding.
predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{}
  
predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{}

method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
{}




// Tossed File 14:
// filename: dafny-synthesis_task_id_807_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_807_no_hints.dfy
// keepToss: TOSS
// reasoning: The specification is too simple - it's a straightforward linear search for the first odd number in an array, which doesn't meaningfully test advanced reasoning or algorithmic thinking beyond basic iteration and conditional logic.
predicate IsOdd(x: int)
{
    x % 2 != 0
}

method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
{}


// Tossed File 15:
// filename: dafny-duck_tmp_tmplawbgxjo_p4_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-duck_tmp_tmplawbgxjo_p4_no_hints.dfy
// keepToss: TOSS
// reasoning: This specification is too simple as it only requires concatenating two arrays, which is a trivial operation that doesn't meaningfully test programming ability or reasoning skills.
//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]

{}

method Main()
{}







