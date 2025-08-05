// Kept File 1:
// filename: dafny-synthesis_task_id_728_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_728_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: Simple element-wise addition of two sequences with clear preconditions and postconditions, appropriate difficulty level for beginners, and well-defined specification.

method AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{}
// Kept File 2:
// filename: Clover_online_max_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_online_max_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This specification defines an online maximum algorithm that finds the maximum in a prefix while determining an optimal stopping point, with clear preconditions, postconditions, and a well-defined algorithmic problem of appropriate difficulty.

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}


// Kept File 3:
// filename: cs245-verification_tmp_tmp0h_nxhqp_quicksort-partition_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/cs245-verification_tmp_tmp0h_nxhqp_quicksort-partition_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This is a well-specified quicksort partition method with clear purpose, appropriate difficulty level, proper requires/ensures clauses, and good documentation. The method name is descriptive and the specifications correctly capture the partitioning behavior including permutation preservation.

// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...
   
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
/*Pre-Condition*/   requires X.Length>=1 && n == X.Length;
/*Post-Condition*/  ensures b>=n;
                    ensures forall x:: 0<=x<a<n ==> X[x] <= p;
                    ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
                    ensures multiset(X[..])==multiset(old(X[..]))           //This says the new X is a permutation of our old version of X.
{}

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */


// Kept File 4:
// filename: dafny-synthesis_task_id_776_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_776_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: Clear method name and purpose (counting vowels with vowel neighbors), appropriate difficulty level, well-specified with requires/ensures, and represents a cohesive string processing problem.

predicate IsVowel(c: char)
{}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{}
// Kept File 5:
// filename: feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This specification defines a well-structured selection sort implementation with clear method names, comprehensive pre/postconditions, and appropriate difficulty level for intermediate programmers. The methods work together coherently toward sorting an array, with proper specifications for sortedness checking and minimum element finding.

/* 
* Formal verification of the selection sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
  modifies a
  ensures isSorted(a, 0, a.Length) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{}

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
  requires 0 <= from < to <= a.Length
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{}

method testSelectionSort() {}

method testFindMin() {}

// Kept File 6:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise4_Find_Max_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise4_Find_Max_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The specification defines a clear findMax method with descriptive naming, proper preconditions and postconditions, appropriate difficulty level for finding maximum element in an array, and well-formed English specifications.

method findMax(a:array<int>) returns (pos:int, maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  ensures exists i :: 0 <= i < a.Length &&  a[i] == maxVal;
  ensures 0 <= pos < a.Length
  ensures a[pos] == maxVal;
{}

// Kept File 7:
// filename: dafny-synthesis_task_id_445_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_445_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The specification defines element-wise multiplication of two sequences with clear preconditions and postconditions, represents a useful programming problem of appropriate difficulty, and has a descriptive method name.

method MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{}
// Kept File 8:
// filename: Clover_find_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_find_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This is a well-specified linear search algorithm with clear method name, comprehensive postconditions covering both success and failure cases, and appropriate difficulty level for intermediate programmers.

method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
{}

// Kept File 9:
// filename: dafny-synthesis_task_id_567_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_567_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This specification checks if an array is sorted, which is a fundamental programming concept with clear, descriptive naming and complete requires/ensures clauses that are neither too trivial nor too difficult.

method IsSorted(a: array<int>) returns (sorted: bool)
    requires a.Length > 0
    ensures sorted <== forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures !sorted ==> exists i, j :: 0 <= i < j < a.Length && a[i] > a[j]
{}
// Kept File 10:
// filename: dafny-synthesis_task_id_230_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_230_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The method has a clear, descriptive name and purpose (replacing blank spaces with a specified character), includes proper requires/ensures specifications with well-defined postconditions, represents a moderately useful string manipulation problem that's neither trivial nor overly complex, and is appropriately scoped for a programmer with 1-2 years of experience.

method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{}
// Kept File 11:
// filename: Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The specification defines string algorithms (prefix, substring, common substring operations) with clear naming, reasonable difficulty level, comprehensive requires/ensures clauses, and cohesive functionality focused on string matching problems.

// We spent 2h each on this assignment

predicate isPrefixPred(pre:string, str:string)
{}

predicate isNotPrefixPred(pre:string, str:string)
{}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{}
predicate isSubstringPred(sub:string, str:string)
{}

predicate isNotSubstringPred(sub:string, str:string)
{}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{}




// Kept File 12:
// filename: Dafny-Exercises_tmp_tmpjm75muf__Session8Exercises_ExerciseInsertionSort_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-Exercises_tmp_tmpjm75muf__Session8Exercises_ExerciseInsertionSort_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The specification defines insertion sort with clear naming, well-defined sorting predicate, and proper ensures clauses including both sortedness and permutation preservation. The predicate body is missing but that doesn't affect usefulness for benchmarking.


predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{}






// Kept File 13:
// filename: dafny-synthesis_task_id_62_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_62_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This spec finds the minimum element in a non-empty array with clear naming, well-defined purpose, appropriate difficulty level, and proper requires/ensures clauses that correctly specify the postconditions for a minimum-finding algorithm.

method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{}
// Kept File 14:
// filename: Clover_copy_part_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_copy_part_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: This is a well-specified array copying method with clear preconditions and postconditions that ensure proper bounds checking and correct copying behavior. The method name is descriptive, the purpose is clear, and it represents a common programming task at an appropriate difficulty level.

method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{}

// Kept File 15:
// filename: dafny-synthesis_task_id_426_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_426_no_hints.dfy
// keepToss: KEEP
// violated: NONE
// reasoning: The specification has a clear, descriptive method name, well-defined purpose (filtering odd numbers), appropriate difficulty level for intermediate programmers, and proper ensures clauses. The predicate and method work together toward the common goal of filtering odd numbers from an array.

/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{}
// Tossed File 1:
// filename: Formal-Methods-Project_tmp_tmphh2ar2xv_Factorial_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Formal-Methods-Project_tmp_tmphh2ar2xv_Factorial_no_hints.dfy
// keepToss: TOSS
// violated: 4, 6, 7
// reasoning: The factorial method is too trivial with missing ensures clause, lacks conceptual cohesion with just one meaningful method, and Main method has no specifications.

method Fact(x: int) returns (y: int)
  requires x >= 0;   
{}
method Main() {}




// Tossed File 2:
// filename: formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs2_hw1_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs2_hw1_no_hints.dfy
// keepToss: TOSS
// violated: 4, 7
// reasoning: This is a trivial homework exercise about basic arithmetic properties with missing specifications for core predicates and functions, making it too simple for a meaningful benchmark.
/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
{}

predicate Odd(m: Nat)
{}


predicate Even(m: Nat)
{}


lemma SumMNIsEven(m: Nat, n: Nat)
requires Odd(m)
requires Odd(n)
ensures Even(add(m,n))
{}



// Tossed File 3:
// filename: type-definition_tmp_tmp71kdzz3p_final_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/type-definition_tmp_tmp71kdzz3p_final_no_hints.dfy
// keepToss: TOSS
// violated: 1, 4, 7
// reasoning: The specification lacks descriptive method names, has trivial empty function bodies, and methods/predicates are missing requires/ensures clauses making it incomplete for benchmarking purposes.
// -------------------------------------------------------------
// 1. Implementing type inference
// -------------------------------------------------------------

// Syntax:
//
// τ := Int | Bool | τ1->τ2
// e ::= x | λx : τ.e | true| false| e1 e2 | if e then e1 else e2
// v ::= true | false | λx : τ.e
// E ::= [·] | E e | v E | if E then e1 else e2
type VarName = string

type TypeVar = Type -> Type

datatype Type = Int | Bool | TypeVar

datatype Exp =
    | Var(x: VarName)
    | Lam(x: VarName, t: Type, e: Exp)
    | App(e1: Exp, e2:Exp)
    | True()
    | False()
    | Cond(e0: Exp, e1: Exp, e2: Exp)

datatype Value =
    | TrueB()
    | FalseB()
    | Lam(x: VarName, t: Type, e: Exp)

datatype Eva = 
    | E()
    | EExp(E : Eva, e : Exp)
    | EVar(v : Value, E : Eva)
    | ECond(E:Eva, e1 : Exp, e2 : Exp)

function FV(e: Exp): set<VarName> {}
// Typing rules system
// -------------------------------------------------------------
// Typing rules system
type Env = map<VarName, Type>

predicate hasType(gamma: Env, e: Exp, t: Type)
{}

// -----------------------------------------------------------------
// 2. Extending While with tuples
// -----------------------------------------------------------------


/*lemma {:induction false} extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma, e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma[x1 := t1], e, t)
{}    */



// Tossed File 4:
// filename: Clover_multi_return_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_multi_return_no_hints.dfy
// keepToss: TOSS
// violated: 4
// reasoning: The problem is too trivial as it only performs basic arithmetic operations (addition and subtraction) without any meaningful logic or algorithmic complexity.
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{}



// Tossed File 5:
// filename: Dafny_Verify_tmp_tmphq7j0row_dataset_error_data_real_error_IsEven_success_1_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_dataset_error_data_real_error_IsEven_success_1_no_hints.dfy
// keepToss: TOSS
// violated: 4, 6, 7
// reasoning: The problem is too trivial (just checking if a number is even), lacks conceptual coherence between function and method, and the function 'even' is missing proper ensures specification.
function even(n: int): bool
  requires n >= 0
{}

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{}



// Tossed File 6:
// filename: dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_DividedConstructors_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_DividedConstructors_no_hints.dfy
// keepToss: TOSS
// violated: 1, 2, 4, 7
// reasoning: This file contains mostly empty class definitions and constructors/methods without any specifications, making it trivial and lacking clear purpose or requires/ensures clauses.
// RUN: %dafny /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {}

module M0 {
  class MyClass {}
}

module M1 refines M0 {
  class MyClass ... {}
}

module TypeOfThis {
  class LinkedList<T(0)> {
    ghost var Repr: set<LinkedList<T>>
    ghost var Rapr: set<LinkedList?<T>>
    ghost var S: set<object>
    ghost var T: set<object?>

    constructor Init()
    {}

    constructor Init'()
    {}

    constructor Create()
    {}

    constructor Create'()
    {}

    constructor Two()
    {}

    method Mutate()
      modifies this
    {}
  }
}

module Regression {
  class A {}
}





// Tossed File 7:
// filename: dafny_tmp_tmp49a6ihvk_m4_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny_tmp_tmp49a6ihvk_m4_no_hints.dfy
// keepToss: TOSS
// violated: 1, 2, 7
// reasoning: The predicate `Below` lacks a body making its purpose unclear, and it's missing requires/ensures clauses, while the method name could be more descriptive about what it actually does.
datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{}



method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{}



// Tossed File 8:
// filename: dafny-synthesis_task_id_624_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_624_no_hints.dfy
// keepToss: TOSS
// violated: 2, 4
// reasoning: The predicates and function lack specifications making their purpose unclear, and the problem of converting strings to uppercase is too trivial for a programming benchmark.
predicate IsLowerCase(c : char)
{}

predicate IsLowerUpperPair(c : char, C : char)
{}

function ShiftMinus32(c : char) :  char
{}

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{}



// Tossed File 9:
// filename: DafnyPrograms_tmp_tmp74_f9k_c_map-multiset-implementation_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/DafnyPrograms_tmp_tmp74_f9k_c_map-multiset-implementation_no_hints.dfy
// keepToss: TOSS
// violated: 7
// reasoning: The Contains predicate in the trait has an empty body and no specification, and several methods in the implementation class lack proper specifications despite having complex behavior, violating the requirement that all methods include requires and ensures clauses.
/**
  This ADT represents a multiset.
 */
trait MyMultiset {

  // internal invariant
  ghost predicate Valid()
    reads this

  // abstract variable
  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  {}

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange

  method Length() returns (len: int)
    requires Valid()
    ensures Valid()
    ensures len == |theMultiset|

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
}

/**
This implementation implements the ADT with a map.
 */
class MultisetImplementationWithMap extends MyMultiset {

  // valid invariant predicate of the ADT implementation
  ghost predicate Valid()
    reads this
  {}

  // the abstraction function
  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  // lemma for the opposite of the abstraction function
  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  // ADT concrete implementation variable
  var elements: map<int, nat>;

  // constructor of the implementation class that ensures the implementation invariant
  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {}
//adds an element to the multiset
  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures elem in elements ==> elements == elements[elem := elements[elem]]
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures !(elem in elements) ==> elements == elements[elem := 1]
    ensures didChange
    ensures Contains(elem)
    ensures Valid()
  {}

//removes an element from the multiset
  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
   /* If the multiset contains the element */
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    /* If the multiset does not contain the element */
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {}

//gets the length of the multiset
  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {}

//compares the current multiset with another multiset and determines if they're equal
  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {}

//gets the elements of the multiset as a sequence
  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {}

//Transforms a map to a sequence
  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {}

  method Test1()
    modifies this
  {}

  method Test2()
    modifies this
  {}

  method Test3()
  {}
}



// Tossed File 10:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny0_snapshots_Inputs_Snapshots0_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny0_snapshots_Inputs_Snapshots0_no_hints.dfy
// keepToss: TOSS
// violated: 4, 7
// reasoning: The methods have non-descriptive names (foo, bar), the purpose is unclear, and the specification is trivial with bar() having an impossible postcondition (ensures false) while foo() lacks any specification.
method foo()
{
  bar();
}

method bar()
  ensures false;




// Tossed File 11:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny4_Primes_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny4_Primes_no_hints.dfy
// keepToss: TOSS
// violated: 7
// reasoning: The specification lacks requires and ensures clauses for most predicates and functions, violating criterion 7. Many key definitions like IsPrime, AllPrimes, product, and PickLargest have empty bodies with no specifications.
// RUN: %testDafnyForEachResolver "%s"


ghost predicate IsPrime(n: int)
{}

// The following theorem shows that there is an infinite number of primes
lemma AlwaysMorePrimes(k: int)
  ensures exists p :: k <= p && IsPrime(p)
{}

// Here is an alternative formulation of the theorem
lemma NoFiniteSetContainsAllPrimes(s: set<int>)
  ensures exists p :: IsPrime(p) && p !in s
{}

// ------------------------- lemmas and auxiliary definitions

ghost predicate AllPrimes(s: set<int>, bound: int)
{}

lemma GetLargerPrime(s: set<int>, bound: int) returns (p: int)
  requires AllPrimes(s, bound)
  ensures bound < p && IsPrime(p)
{}

ghost function product(s: set<int>): int
{}

lemma product_property(s: set<int>)
  requires forall x :: x in s ==> 1 <= x
  ensures 1 <= product(s) && forall x :: x in s ==> x <= product(s)
{}

lemma ProductPlusOneIsPrime(s: set<int>, q: int)
  requires AllPrimes(s, q) && q == product(s)
  ensures IsPrime(q+1)
{}

// The following lemma is essentially just associativity and commutativity of multiplication.
// To get this proof through, it is necessary to know that if x!=y and y==Pick...(s), then
// also y==Pick...(s - {x}).  It is for this reason that we use PickLargest, instead of
// picking an arbitrary element from s.
lemma RemoveFactor(x: int, s: set<int>)
  requires x in s
  ensures product(s) == x * product(s - {x})
{}

// This definition is like IsPrime above, except that the quantification is only over primes.
ghost predicate IsPrime_Alt(n: int)
{}

// To show that n is prime, it suffices to prove that it satisfies the alternate definition
lemma AltPrimeDefinition(n: int)
  requires IsPrime_Alt(n)
  ensures IsPrime(n)
{}

lemma Composite(c: int) returns (a: int, b: int)
  requires 2 <= c && !IsPrime(c)
  ensures 2 <= a < c && 2 <= b && a * b == c
  ensures IsPrime(a)
{}

ghost function PickLargest(s: set<int>): int
  requires s != {}
{}

lemma LargestElementExists(s: set<int>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
{}

lemma MulPos(a: int, b: int)
  requires 1 <= a && 1 <= b
  ensures a <= a * b
{}

// This axiom about % is needed.  Unfortunately, Z3 seems incapable of proving it.
lemma MulDivMod(a: nat, b: nat, c: nat, j: nat)
  requires a * b == c && j < a
  ensures (c+j) % a == j




// Tossed File 12:
// filename: Clover_triple3_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Clover_triple3_no_hints.dfy
// keepToss: TOSS
// violated: 4
// reasoning: The problem is far too trivial - it only requires multiplying a number by 3, which is an extremely basic arithmetic operation that doesn't provide meaningful programming challenge.
method Triple (x:int) returns (r:int)
  ensures r==3*x
{}



// Tossed File 13:
// filename: Dafny-programs_tmp_tmpnso9eu7u_Algorithms + sorting_bubble-sort_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/Dafny-programs_tmp_tmpnso9eu7u_Algorithms + sorting_bubble-sort_no_hints.dfy
// keepToss: TOSS
// violated: 7
// reasoning: The predicates sorted_between and sorted lack requires and ensures clauses, and they have empty bodies which makes their purpose unclear without proper specifications.
/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{}

predicate sorted(A:array<int>)
    reads A
{}

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{}

method Main() {}

/* Explanation:

     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/



// Tossed File 14:
// filename: dafny-synthesis_task_id_622_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_622_no_hints.dfy
// keepToss: TOSS
// violated: 7
// reasoning: The method lacks proper ensures clause - the current ensures doesn't correctly specify finding the median of two sorted arrays, and appears to have a logic error mixing elements from both arrays incorrectly.
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
{}


// Tossed File 15:
// filename: dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// filepath: /Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed/dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// keepToss: TOSS
// violated: 4, 7
// reasoning: The problem is too trivial (just filtering vowels from an array), the vowels set is empty making it nonsensical, and the function FilterVowels lacks requires/ensures clauses.
//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}



