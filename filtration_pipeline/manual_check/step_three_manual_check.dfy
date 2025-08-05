// Kept File 1:
// filename: Clover_longest_prefix_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_longest_prefix_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 0
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}

// Kept File 2:
// filename: dafny-synthesis_task_id_741_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_741_no_hints.dfy
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

method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{}
// Kept File 3:
// filename: Dafny_Verify_tmp_tmphq7j0row_dataset_detailed_examples_SelectionSort_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_dataset_detailed_examples_SelectionSort_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 0
// num_lines: 10
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

// Kept File 4:
// filename: dafny-synthesis_task_id_262_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_262_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 1
// num_lines: 6
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}
// Kept File 5:
// filename: dafny-synthesis_task_id_457_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_457_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{}
// Kept File 6:
// filename: dafny-synthesis_task_id_632_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_632_no_hints.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 8
// num_requires: 3
// num_lines: 30
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
{}

method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{}


// Kept File 7:
// filename: Clover_modify_2d_array_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_modify_2d_array_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 3
// num_lines: 10
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j:nat :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures  arr[index1][index2] == val
{}

// Kept File 8:
// filename: Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 9
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{}


// Kept File 9:
// filename: Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_tmp_tmp0wu8wmfr_Heimaverkefni 2_BinarySearchDec_no_hints.dfy
// num_methods: 3
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 6
// num_requires: 5
// num_lines: 41
// num_no_ensures: 1
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;

{}

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{}

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.
method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
{}

// Kept File 10:
// filename: dafny-synthesis_task_id_733_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_733_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 2
// num_lines: 7
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}
// Kept File 11:
// filename: dafny-synthesis_task_id_776_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_776_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 2
// num_requires: 0
// num_lines: 7
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

predicate IsVowel(c: char)
{}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{}
// Kept File 12:
// filename: dafny-synthesis_task_id_627_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_627_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 2
// num_lines: 7
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
{}
// Kept File 13:
// filename: Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Minimum_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Minimum_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 6
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method Minimum(a: array<int>) returns (m: int) 
	requires a.Length > 0
	ensures exists i :: 0 <= i < a.Length && m == a[i]
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{}

// Kept File 14:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_MajorityVote_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_MajorityVote_no_hints.dfy
// num_methods: 5
// num_lemmas: 2
// num_classes: 0
// num_functions: 1
// num_predicates: 1
// num_ensures: 8
// num_requires: 9
// num_lines: 130
// num_no_ensures: 1
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

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


// Kept File 15:
// filename: Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_no_hints.dfy
// num_methods: 3
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 3
// num_lines: 17
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


// Tossed File 1:
// filename: AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/AssertivePrograming_tmp_tmpwf43uz0e_DivMode_Unary_no_hints.dfy
// num_methods: 3
// num_lemmas: 12
// num_classes: 0
// num_functions: 5
// num_predicates: 2
// num_ensures: 15
// num_requires: 8
// num_lines: 231
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

predicate Less(x: Unary, y: Unary) {}

predicate LessAlt(x: Unary, y: Unary) {}

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
{
  calc{
    Add(Mul(Suc(d), y), Sub(x0, y));
    == {AddMulEqMulSuc(d, y);
    Add(Add(Mul(d, y), y), Sub(x0, y));
    == {AddTransitive(Mul(d, y), y, Sub(x0, y));
    Add(Mul(d, y), Add(y, Sub(x0, y)));
    == {AddCommutative(Sub(x0, y), y);
    Add(Mul(d, y), Add(Sub(x0, y), y));
    == {assert !Less(x0, y);
        AddSub(x0, y);
    Add(Mul(d, y), x0);
  }
}

lemma AddTransitive(a: Unary, b: Unary, c: Unary)
  ensures Add(a, Add(b, c)) == Add(Add(a, b), c)
{//These assertions are only for documanting the proof obligations
  match c 
  case Zero =>
    calc{
      Add(a, Add(b, c));
      == 
      Add(a, Add(b, Zero));
      == // def. Add
      Add(a, b);
      == // def. Add
      Add(Add(a,b), Zero);
      == 
      Add(Add(a,b), c);
    }
  case Suc(c') =>
    match b
    case Zero =>
      calc{
        Add(a, Add(b, c));
        == 
        Add(a, Add(Zero, Suc(c')));
        == {AddZero(Suc(c'));
        Add(a, Suc(c'));
        == // def. Add
        Add(Add(a, Zero), Suc(c'));
        ==
        Add(Add(a, b), Suc(c'));
        ==
        Add(Add(a,b), c);
      }
    case Suc(b') =>
      match a
      case Zero =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Zero, Add(Suc(b'), Suc(c')));
          == {AddZero(Add(Suc(b'), Suc(c')));
          Add(Suc(b'), Suc(c'));
          == {AddZero(Suc(b'));
          Add(Add(Zero, Suc(b')), Suc(c'));
          ==
          Add(Add(a, b), c);
        }
      case Suc(a') =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Suc(a'), Add(Suc(b'), Suc(c')));
          == // def. Add
          Add(Suc(a'), Suc(Add(Suc(b'), c')));
          == // def. Add
          Suc(Add(Suc(a'), Add(Suc(b'), c')));
          == {SucAdd(a', Add(Suc(b'), c'));
          Suc(Suc(Add(a', Add(Suc(b'), c'))));
          == {SucAdd(b', c');
          Suc(Suc(Add(a', Suc(Add(b', c')))));
          == // def. Add
          Suc(Suc(Suc(Add(a', Add(b', c')))));
          == {AddTransitive(a', b', c');
          Suc(Suc(Suc(Add(Add(a',b'), c'))));
          == // def. Add
          Suc(Suc(Add(Add(a', b'), Suc(c'))));
          == {SucAdd(Add(a', b'), Suc(c'));
          Suc(Add(Suc(Add(a', b')), Suc(c')));
          == {SucAdd(a', b');
          Suc(Add(Add(Suc(a'), b'), Suc(c')));
          == {SucAdd(Add(Suc(a'), b'), Suc(c'));
          Add(Suc(Add(Suc(a'), b')), Suc(c'));
          == // def. Add
          Add(Add(Suc(a'), Suc(b')), Suc(c'));
          ==
          Add(Add(a,b), c);
        }

}

lemma AddCommutative(a: Unary, b: Unary)
  ensures Add(a, b) == Add(b, a)
{
  match b
  case Zero => 
    calc{
      Add(a, b);
      ==
      Add(a, Zero);
      == // def. Add
      a;
      == {AddZero(a);
      Add(Zero, a);
      ==
      Add(b, a);
    }
  case Suc(b') =>
    calc{
      Add(a, b);
      ==
      Add(a, Suc(b'));
      == // def. Add
      Suc(Add(a, b'));
      == {AddCommutative(a, b');
      Suc(Add(b', a));
      == {SucAdd(b', a);
      Add(Suc(b'), a);
      ==
      Add(b, a);
    }
}



method Main() {
  var U3 := Suc(Suc(Suc(Zero)));
  var U7 := Suc(Suc(Suc(Suc(U3))));
  var d, m := IterativeDivMod(U7, U3);
  print "Just as 7 divided by 3 is 2 with a remainder of 1, IterativeDivMod(", U7, ", ", U3, ") is ", d, " with a remainder of ", m;
}



