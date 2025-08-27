// Kept File 1:
// filename: Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Software-Verification_tmp_tmpv4ueky2d_Remove Duplicates from Sorted Array_remove_duplicates_from_sorted_array_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "remove_duplicates_from_sorted_array" clearly indicates its purpose is to remove duplicate elements from a sorted array, making the specification interpretable.

method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{}


// Helper predicate
predicate is_sorted(nums: seq<int>)
{}

predicate is_sorted_and_distinct(nums: seq<int>)
{}


// Kept File 2:
// filename: dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// keepToss: KEEP
// reasoning: The predicate and method names "triple" and "GetTriple" along with the specifications clearly indicate this is about finding three consecutive equal elements in an array.

predicate triple(a: array<int>) 
reads a
{}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{}

method TesterGetTriple()
{}


// Kept File 3:
// filename: SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "GetEven" and the ensures clause clearly indicate this method is supposed to make all elements in the array even numbers.

// successfully verifies
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}

// Kept File 4:
// filename: iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// keepToss: KEEP
// reasoning: The module defines a framework for sharded state machines with clear purpose indicated by the name and extensive documentation explaining its components and requirements.

// General form of a ShardedStateMachine
// To instantiate one, fill in the 'Shard' type, the 'glue' function
// provide the 'Next' predicate and the invariant 'Inv',
// and then meet various proof obligations in the form of lemmas.

abstract module ShardedStateMachine {
  /*
   * A ShardedStateMachine contains a 'Shard' type that represents
   * a shard of the state machine.
   */

  type Shard

  predicate valid_shard(a: Shard)

  /*
   * There must be some notion that lets us put two shards together.
   */

  function glue(a: Shard, b: Shard) : Shard

  /*
   * The 'glue' operation must respect monoidal laws.
   */

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))

  function unit() : Shard
  ensures valid_shard(unit())

  lemma glue_unit(a: Shard)
  ensures glue(a, unit()) == a

  /*
   * The invariant is meant to be a predicate over a 'whole' shard,
   * that is, all the pieces glued together at once.
   */

  predicate Inv(s: Shard)

  /*
   * 'Next' predicate of our state machine.
   */

  predicate Next(shard: Shard, shard': Shard)

  lemma NextPreservesValid(s: Shard, s': Shard)
  requires valid_shard(s)
  requires Next(s, s')
  ensures valid_shard(s')

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
  requires Next(s, s')
  requires valid_shard(glue(s, t))
  requires Next(glue(s, t), glue(s', t))

  /*
   * The operation must preserve the state machine invariant.
   */

  lemma NextPreservesInv(s: Shard, s': Shard)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
}


// Kept File 5:
// filename: dafny-synthesis_task_id_262_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_262_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "SplitArray" and the specification clearly indicate it splits an array into two parts at index L.

method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}
// Kept File 6:
// filename: dafny-synthesis_task_id_808_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_808_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "ContainsK" and parameters clearly indicate it checks whether element k is contained in sequence s.

method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{}
// Kept File 7:
// filename: dafny-synthesis_task_id_809_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_809_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "IsSmaller" and the ensures clauses make it clear this is checking if all elements in sequence a are greater than corresponding elements in sequence b.

method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
    requires |a| == |b|
    ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
    ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{}
// Kept File 8:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example_no_hints.dfy
// keepToss: KEEP
// reasoning: The function names like `contains`, `intersect`, `union`, and `overlap` clearly indicate their intended purpose for interval operations.

/* Here's a small but realistic setting where you could use Dafny.

   The setting is that we're implementing an interval library that manages a
   data structure with a low and a high value. It implements some computations
   on intervals, and we want to make sure those are right.
 */

// Interval is the Dafny model of the data structure itself. We're using `real`
// here for the numbers; the specifics don't really matter, as long as we can
// compare them with <.
datatype Interval = Interval(lo: real, hi: real)

// Contains is one of the core operations on intervals, both because we support
// it in the API and because in some ways it defines what the interval means.
predicate contains(i: Interval, r: real) {}

// We also provide a way to check if an interval is empty.
predicate empty(i: Interval) {
  i.lo > i.hi
}

/* Now we can already do our first proof! Empty is a way to check if an interval
 * doesn't contain any numbers - let's prove that empty and contains agree with
 * each other. */

lemma empty_ok(i: Interval)
  // this is the sort of property that's easy to express logically but hard to test for
  ensures empty(i) <==> !exists r :: contains(i, r)
{}

// min and max are just helper functions for the implementation
function min(r1: real, r2: real): real {}

function max(r1: real, r2: real): real {}

/* The first complicated operation we expose is a function to intersect two
 * intervals. It's not so easy to think about whether this is correct - for
 * example, does it handle empty intervals correctly? Maybe two empty intervals
 * could intersect to a non-empty one? */

function intersect(i1: Interval, i2: Interval): Interval {}

// This theorem proves that intersect does exactly what we wanted it to, using
// `contains` as the specification.
lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

/* Next we'll define the union of intervals. This is more complicated because if
 * the intervals have no overlap, a single interval can't capture their union
 * exactly. */

// Intersect gives us an easy way to define overlap, and we already know it
// handles empty intervals correctly.
predicate overlap(i1: Interval, i2: Interval) {}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
{}

// We'll give this function a precondition so that it always does the right thing.
function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{}

// We can prove union correct in much the same way as intersect, with a similar
// specification, although notice that now we require that the intervals
// overlap.
lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

// Though not used elsewhere here, if two intervals overlap its possible to show
// that there's a common real contained in both of them. We also show off new
// syntax: this lemma returns a value which is used in the postcondition, and
// which the calling lemma can make use of.
lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{}

/* One extension you might try is adding is an operation to check if an interval
 * is contained in another and proving that correct. Or, try implementing a
 * similar library for 2D rectangles. */


// Kept File 9:
// filename: Clover_two_sum_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_two_sum_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "twoSum" clearly indicates it finds two array elements that sum to a target value, and the specification confirms this purpose.

method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{}

// Kept File 10:
// filename: cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "BubbleSort" clearly indicates it's supposed to sort an array using the bubble sort algorithm.

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 
// The following is just plain old bubble sort.
//
// Can you find the invariants for the while loops?
// Can you annotate this?
// What about the pre/post-conditions?

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{}

/*Doesn't my title look all bubbly and cute? I'm trying... */


// Kept File 11:
// filename: dafny-synthesis_task_id_424_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_424_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "ExtractRearChars" clearly indicates it extracts the last characters from strings, and the specification confirms this purpose.

method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{}
// Kept File 12:
// filename: SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/SENG2011_tmp_tmpgk5jq85q_flex_ex2_no_hints.dfy
// keepToss: KEEP
// reasoning: The function and method names clearly indicate their purposes: maxcheck appears to check something related to maximum values, max finds the maximum element in an array, and Checker performs some checking operation.

function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{}

method Checker() {}

// Kept File 13:
// filename: dafny-synthesis_task_id_94_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_94_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name and postcondition clearly indicate it finds the first element of the sequence that has the minimum second element.

method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{}
// Kept File 14:
// filename: Clover_longest_prefix_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_longest_prefix_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "LongestCommonPrefix" clearly indicates it should find the longest common prefix of two character sequences, making the purpose interpretable.

method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}

// Kept File 15:
// filename: dafny-synthesis_task_id_750_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_750_no_hints.dfy
// keepToss: KEEP
// reasoning: The method name "AddTupleToList" clearly indicates it adds a tuple to a list, and the specification confirms this purpose.

method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
}
// Tossed File 1:
// filename: Dafny_Programs_tmp_tmp99966ew4_trig_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_Programs_tmp_tmp99966ew4_trig_no_hints.dfy
// keepToss: TOSS
// reasoning: The method name "test" and the abstract predicates P and Q provide no interpretable context for what this method is supposed to accomplish.
predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
}



// Tossed File 2:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67_no_hints.dfy
// keepToss: TOSS
// reasoning: The names "AuxMethod" and "MainMethod" are generic and provide no indication of what these methods are supposed to accomplish.
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{}




