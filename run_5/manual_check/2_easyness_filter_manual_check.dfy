// Kept File 1:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_ListReverse.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_ListReverse.dfy
// keepToss: KEEP
// reasoning: This involves linked list reversal logic with pointer manipulation and invariant maintenance, which is not a direct formula.

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r;
    requires (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    modifies r;
    ensures reverse == null || reverse in r;
    ensures (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    decreases *;
  {}
}


// Kept File 2:
// filename: formal-verification_tmp_tmpoepcssay_strings3.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/formal-verification_tmp_tmpoepcssay_strings3.dfy
// keepToss: KEEP
// reasoning: This specification involves complex string operations, substring searching, and logical reasoning that is not a direct formula.

predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures  res ==> isSubstringPred(sub, str)
	// ensures  !res ==> !isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{}



predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{}



// Kept File 3:
// filename: Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower.dfy
// keepToss: KEEP
// reasoning: This involves implementing a power function which requires iterative or recursive logic, not a direct formula.

function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}

// Kept File 4:
// filename: Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy
// keepToss: KEEP
// reasoning: This involves solving a system of linear equations to find X and Y from p and q, which is not a direct formula.

// problem 2:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXX

method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{}


// Kept File 5:
// filename: DafnyProjects_tmp_tmp2acw_s4s_CombNK.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/DafnyProjects_tmp_tmp2acw_s4s_CombNK.dfy
// keepToss: KEEP
// reasoning: This specification involves dynamic programming implementation with recursive definitions and lemmas, which is not a direct formula.


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




// Kept File 6:
// filename: dafny-synthesis_task_id_126.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_126.dfy
// keepToss: KEEP
// reasoning: This is not a direct formula as it requires finding and summing all common divisors, which involves iterative logic or mathematical reasoning beyond a single formula.

method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{}
// Kept File 7:
// filename: FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/FormalMethods_tmp_tmpvda2r3_o_dafny_Invariants_ex2.dfy
// keepToss: KEEP
// reasoning: The specification involves exponentiation with loop invariants and iterative computation logic, which is not a direct formula.

function Potencia(x:nat, y:nat):nat
{}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{}
/*
Inv = 
Pot(2,3)
Teste de mesa
x   y   b   e   r           Inv --> b^e * r = x^y
2   3   2   3   1           2^3 * 2^0 = 2^3
2   3   2   2   1*2         2^2 * 2^1 = 2^3
2   3   2   1   1*2*2       2^1 * 2^2 = 2^3
2   3   2   0   1*2*2*2     2^0 * 2^3 = 2^3
*/

// Kept File 8:
// filename: ProjectosCVS_tmp_tmp_02_gmcw_Handout 1_CVS_handout1_55754_55780.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/ProjectosCVS_tmp_tmp_02_gmcw_Handout 1_CVS_handout1_55754_55780.dfy
// keepToss: KEEP
// reasoning: This specification involves implementing multiplication and division algorithms with loop invariants and mathematical reasoning, not a direct formula.

/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {}

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {}


//Second Exercise
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
    {}


// Kept File 9:
// filename: dafny_examples_tmp_tmp8qotd4ez_leetcode_0277-find-the-celebrity.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny_examples_tmp_tmp8qotd4ez_leetcode_0277-find-the-celebrity.dfy
// keepToss: KEEP
// reasoning: This involves logical reasoning about celebrity relationships and quantified predicates, not a direct formula.

// Author: Shaobo He

predicate knows(a: int, b: int)

predicate isCelebrity(n : int, i : int)
requires n >= 0 && 0 <= i < n;
{
    forall j :: 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j)
}

lemma knowerCannotBeCelebrity(n: int, i: int)
requires n >= 0 && 0 <= i < n
ensures (exists j :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
{}

ghost method isCelebrityP(n: int, i: int) returns (r : bool)
requires n >= 0 && 0 <= i < n;
ensures r <==> isCelebrity(n, i);
{} 

ghost method findCelebrity(n : int) returns (r : int)
requires 2 <= n <= 100;
ensures 0 <= r < n ==> isCelebrity(n, r);
ensures r == -1 ==> forall i :: 0 <= i < n ==> !isCelebrity(n, i);
{}

// Kept File 10:
// filename: Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_normal_data_completion_MaxPerdV2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_normal_data_completion_MaxPerdV2.dfy
// keepToss: KEEP
// reasoning: This specification involves finding the maximum element in an array, which requires comparison logic and is not a direct formula.

function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{}


// Kept File 11:
// filename: Clover_swap_arith.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_swap_arith.dfy
// keepToss: KEEP
// reasoning: This is not a direct formula, as it requires swapping logic to exchange the values of two variables.

method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X

{}

// Kept File 12:
// filename: Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy
// keepToss: KEEP
// reasoning: This is not a direct formula, as it involves method structure with preconditions and postconditions that require implementation logic.

method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{}

// Kept File 13:
// filename: protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_dafny-internals_02-triggers_triggers2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_dafny-internals_02-triggers_triggers2.dfy
// keepToss: KEEP
// reasoning: This specification defines function relationships and axioms with logical reasoning about triggers and function composition, which is not a direct formula.

function f(x: int): int

function ff(x: int): int

lemma {:axiom} ff_eq()
  ensures forall x {:trigger ff(x)} :: ff(x) == f(f(x))

lemma {:axiom} ff_eq2()
  ensures forall x {:trigger f(f(x))} :: ff(x) == f(f(x))

lemma {:axiom} ff_eq_bad()
  // dafny ignores this trigger because it's an obvious loop
  ensures forall x {:trigger {f(x)}} :: ff(x) == f(f(x))

lemma use_ff(x: int)
{}

lemma use_ff2(x: int)
{}


// Kept File 14:
// filename: protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_ch03_nim_v3.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_ch03_nim_v3.dfy
// keepToss: KEEP
// reasoning: This specification defines a Nim game state machine with multiple transitions, player turns, and game logic, which is not a direct formula.

// Nim version 3: fix the bug and demonstrate a behavior.
//
// In this version, we've fixed the bug by actually flipping whose turn it is in
// each transition.

datatype Player = P1 | P2
{}
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn.P1? // syntax
}

datatype Step =
  | TurnStep(take: nat, p: nat)
  | NoOpStep()

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{
  var p := step.p;
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {
  match step {
    case TurnStep(_, _) => Turn(v, v', step)
    case NoOpStep() => v' == v // we don't really need to define predicate NoOp
  }
}

// boilerplate
lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
}

// boilerplate
ghost predicate Next(v: Variables,  v': Variables) {
  exists step :: NextStep(v, v', step)
}

// We'll frequently prove a lemma of this form to show some example of the state
// machine transitioning. You'll prove determinism to avoid accidentally having
// transitions do things they shouldn't. Proofs will show that your state
// machine doesn't do anything bad (note this would also catch unintentional
// non-determinism, but it can be more painful to debug such issues at this
// stage). These example behaviors will prevent bugs where your state machine
// just doesn't do anything, especially because of overly restrictive
// preconditions.
lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| >= 3 // for this example, we just demonstrate there is some execution with three states
  ensures Init(b[0])
  ensures forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1])
{}


// Kept File 15:
// filename: HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Largest Sum_largest_sum.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Largest Sum_largest_sum.dfy
// keepToss: KEEP
// reasoning: This specification requires implementing a maximum subarray sum algorithm, which is not a direct formula.

// CoPilot function converted to dafny
method largest_sum(nums: array<int>, k: int) returns (sum: int)
    requires nums.Length > 0 
    ensures max_sum_subarray(nums, sum, 0, nums.Length)
{}

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
    requires arr.Length > 0
    requires 0 <= start <= stop <= arr.Length
    reads arr
{}


//Sums array elements between [start, stop)
function Sum_Array(arr: array<int>, start: int, stop: int): int
    requires 0 <= start <= stop <= arr.Length
    decreases stop - start
    reads arr
{}





// Tossed File 1:
// filename: dafny-synthesis_task_id_85.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_85.dfy
// keepToss: TOSS
// reasoning: This is a direct formula for sphere surface area (4πr²) with no programming logic or reasoning required.
method SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
{}


// Tossed File 2:
// filename: dafny-synthesis_task_id_233.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_233.dfy
// keepToss: TOSS
// reasoning: This specification computes the lateral surface area of a cylinder using the direct formula 2πrh.
method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
{}


// Tossed File 3:
// filename: Clover_return_seven.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_return_seven.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply returns the constant value 7.
method M(x: int) returns (seven: int)
  ensures seven==7
{
  seven := 7;
}



// Tossed File 4:
// filename: Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that computes n*n with no programming logic or reasoning required.
method square (n: int) returns (r: int)
	requires 0 <= n;
	ensures r == n*n;
{}



// Tossed File 5:
// filename: dafny-synthesis_task_id_304.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_304.dfy
// keepToss: TOSS
// reasoning: The specification reduces to a direct formula: element == l[(index - n + |l|) % |l|].
method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{}


// Tossed File 6:
// filename: Clover_cal_sum.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_cal_sum.dfy
// keepToss: TOSS
// reasoning: This is a direct formula for computing the sum of integers from 1 to N.
method Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{}



// Tossed File 7:
// filename: M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo9-Carre.dfy
// keepToss: TOSS
// reasoning: This specification computes a*a which is a direct formula with no programming logic or reasoning required.
method Carre(a: nat) returns (c: nat)
ensures c == a*a
{}



// Tossed File 8:
// filename: Clover_count_lessthan.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_count_lessthan.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply counts elements in a set meeting a condition.
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{}



// Tossed File 9:
// filename: dafny-synthesis_task_id_238.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_238.dfy
// keepToss: TOSS
// reasoning: This specification is just a direct formula for computing the number of non-empty substrings.
method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{}


// Tossed File 10:
// filename: dafny-synthesis_task_id_626.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_626.dfy
// keepToss: TOSS
// reasoning: This specification computes the area using the direct formula area = radius².
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{}


// Tossed File 11:
// filename: dafny-synthesis_task_id_432.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_432.dfy
// keepToss: TOSS
// reasoning: This specification just computes (a + b) / 2, which is a direct formula.
method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{}


// Tossed File 12:
// filename: dafny-synthesis_task_id_17.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_17.dfy
// keepToss: TOSS
// reasoning: This computes the perimeter of a square using the direct formula 4 * side.
method SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
{}


// Tossed File 13:
// filename: dafny-synthesis_task_id_143.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_143.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply returns the length of the input sequence.
method CountArrays(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
{}


// Tossed File 14:
// filename: Clover_triple4.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_triple4.dfy
// keepToss: TOSS
// reasoning: This is a direct formula that simply multiplies the input by 3.
method Triple (x:int) returns (r:int)
  ensures r==3*x
{}



// Tossed File 15:
// filename: dafny-synthesis_task_id_598.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_598.dfy
// keepToss: TOSS
// reasoning: This specification implements a direct formula for checking if a 3-digit number equals the sum of cubes of its digits.
method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{}


