// Kept File 1:
// filename: Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_Test_Cases_Index.dfy
// keepToss: KEEP
// reasoning: The method names clearly indicate their purposes: Index returns an index within bounds, Min/Max find minimum/maximum values, MaxSum computes both sum and maximum, etc.

method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    i := n/2;
}

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{}

method Max(x: int, y: int) returns (m: int) {}


method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x >= y then x else y
{}


method MaxSumCaller() {}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{}


method TestMaxSum(x: int, y: int) 
{}


// Kept File 2:
// filename: Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_CopyMatrix.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_CopyMatrix.dfy
// keepToss: KEEP
// reasoning: The method name "CopyMatrix" clearly indicates it copies a matrix from source to destination, and the specification confirms this purpose.

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{}

// Kept File 3:
// filename: M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy
// keepToss: KEEP
// reasoning: The method name clearly indicates it should count to n and return n, which aligns with the specification.

method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{}

// Kept File 4:
// filename: dafny-synthesis_task_id_106.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_106.dfy
// keepToss: KEEP
// reasoning: The method name "AppendArrayToSeq" clearly indicates it appends an array to a sequence, and the specification confirms this purpose.

method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{}
// Kept File 5:
// filename: Clover_canyon_search.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_canyon_search.dfy
// keepToss: KEEP
// reasoning: The method name "CanyonSearch" combined with the specification clearly indicates it finds the minimum absolute difference between elements from two sorted arrays.

method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{}


// Kept File 6:
// filename: dafny-synthesis_task_id_436.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_436.dfy
// keepToss: KEEP
// reasoning: The method name "FindNegativeNumbers" and the comment clearly indicate this is supposed to find and return negative numbers from an input array.

/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{}
// Kept File 7:
// filename: dafny-synthesis_task_id_588.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_588.dfy
// keepToss: KEEP
// reasoning: The method name "DifferenceMinMax" and the ensures clause clearly indicate this computes the difference between the maximum and minimum values in an array.

method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == Max(a[..]) - Min(a[..])
{}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{}

function Max(a: seq<int>) : int
    requires |a| > 0
{}


// Kept File 8:
// filename: dafny_examples_tmp_tmp8qotd4ez_leetcode_0001-two-sum.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny_examples_tmp_tmp8qotd4ez_leetcode_0001-two-sum.dfy
// keepToss: KEEP
// reasoning: The method name "TwoSum" and the ensures clauses clearly indicate this is meant to find two indices in an array whose values sum to a target, which is a well-known algorithmic problem.

// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {}
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{}

// Kept File 9:
// filename: FlexWeek_tmp_tmpc_tfdj_3_ex4.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/FlexWeek_tmp_tmpc_tfdj_3_ex4.dfy
// keepToss: KEEP
// reasoning: The method name "join" and the specifications clearly indicate this method is supposed to concatenate two arrays into a single array.

method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

// Forall

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]

{}


method Check(){}

// Kept File 10:
// filename: dafny-synthesis_task_id_309.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_309.dfy
// keepToss: KEEP
// reasoning: The method name "Max" and the ensures clauses clearly indicate this method is supposed to return the maximum of two integers.

method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
{}
// Kept File 11:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_MatrixMultiplication.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_MatrixMultiplication.dfy
// keepToss: KEEP
// reasoning: The function and method names clearly indicate matrix operations - computing row-column products and matrix multiplication.

function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
{}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases m1.Length1 - k
{}

method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
{}


// Kept File 12:
// filename: dafny_examples_tmp_tmp8qotd4ez_lib_math_DivMod.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny_examples_tmp_tmp8qotd4ez_lib_math_DivMod.dfy
// keepToss: KEEP
// reasoning: The module contains division and modulo operations with clear mathematical purpose, even though the functions are opaque.

module DivMod {

  function {:opaque} DivSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {}

  function {:opaque} ModSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {}

  lemma DivModAdd1(a: int, b: int)
    requires b != 0
    ensures (a + b) % b == a % b
    ensures (a + b) / b == a / b + 1
  {}

  lemma DivModSub1(a: int, b: int)
    requires b != 0
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
  {}

  lemma ModEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a % b == ModSub(a, b)
  {}

  lemma DivEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a / b == DivSub(a, b)
  {}

  lemma DivModSpec'(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures ModSub(a, b) == r
    ensures DivSub(a, b) == q
  {}

  lemma DivModSpec(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures a % b == r
    ensures a / b == q
  {}

  lemma DivMul(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a * b / b == a
  {}

  lemma DivModMulAdd(a: int, b: int, c: int)
    requires 0 <= a && 0 <= c < b && 0 < b
    ensures (a * b + c) / b == a
    ensures (a * b + c) % b == c
  {}

}

// Kept File 13:
// filename: dafny-synthesis_task_id_397.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_397.dfy
// keepToss: KEEP
// reasoning: The method name "MedianOfThree" clearly indicates it should return the median value of three integers, making its purpose interpretable.

method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{}
// Kept File 14:
// filename: dafny-synthesis_task_id_282.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_282.dfy
// keepToss: KEEP
// reasoning: The method name "ElementWiseSubtraction" clearly indicates it performs element-wise subtraction between two arrays, which is confirmed by the specification.

method ElementWiseSubtraction(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] - b[i]
{}
// Kept File 15:
// filename: dafny-synthesis_task_id_95.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_95.dfy
// keepToss: KEEP
// reasoning: The method name "SmallestListLength" clearly indicates it finds the length of the smallest sequence within a sequence of sequences, which matches the specification.

method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{}
// Tossed File 1:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny0_ModulePrint.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny0_ModulePrint.dfy
// keepToss: TOSS
// reasoning: The method m() has no clear purpose from its name and the ensures clauses are just tautologies (h == h, j == j) that provide no meaningful specification.
// NONUNIFORM: Tests printing much more than compilation
// RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /dprint:"%t.dfy" "%s" > "%t"
// RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /printMode:DllEmbed /dprint:"%t1.dfy" "%t.dfy" >> "%t"
// RUN: %dafny /env:0 /compile:3 /printMode:DllEmbed /dprint:"%t2.dfy" "%t1.dfy" >> "%t"
// RUN: %diff "%t1.dfy" "%t2.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

abstract module S {
  class C {
    var f: int
    ghost var g: int
    var h: int
    method m()
      modifies this
  }
}

module T refines S {
  class C ... {
    ghost var h: int  // change from non-ghost to ghost
    ghost var j: int
    var k: int
    constructor () { }
    method m()
      ensures h == h
      ensures j == j
    {}
  }
}

method Main() {}




// Tossed File 2:
// filename: formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs4_gr2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/formal-methods-in-software-engineering_tmp_tmpe7fjnek6_Labs4_gr2.dfy
// keepToss: TOSS
// reasoning: The specifications are entirely in Romanian, making them not interpretable in English.
/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

method SqrSum(n: int) returns (s: int)
{}

method DivMod(a: int, b: int) returns (q: int, r: int)
decreases *
{}

/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
method HoareTripleAssmAssrt()
{}

// varianta requires-ensures

method HoareTripleReqEns(i: int, k: int) returns (k': int)
	// (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
	requires  k == i*i
	ensures  k' == (i+1)*(i+1)
{}

/*
regula pentru while
*/

// varianta cu assert
/*
method WhileRule()
{}
*/

// varianta cu invariant
method Invariant1()
{}

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
	requires n >= 0
{}
/*
method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
{
	// ???
}
*/

// verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{}

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
least lemma L1(n: int)
	requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    //OK
}

/*
function SqrSumBy6(n: int) : int
{}

inductive lemma L(n: int) // it takes a while
	decreases n
	requires n >= 0
	ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{}

*/

method DivMod1(a: int, b: int) returns (q: int, r: int)
requires b > 0 && a >= 0
ensures a == b*q + r && 0 <= r < b
//decreases *
{}

method Main()
	decreases *
{}





// Tossed File 3:
// filename: ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old3.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old3.dfy
// keepToss: TOSS
// reasoning: The method name "mm" provides no indication of what the method is supposed to do, and the specification only gives preconditions and modifies clauses without any postconditions to clarify its purpose.
class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    requires z1.Length > 10 && z1[0] == 7
    requires z2.Length > 10 && z2[0] == 17
    modifies z2
  {}
}




// Tossed File 4:
// filename: ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_git-issues_git-issue-1158.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_git-issues_git-issue-1158.dfy
// keepToss: TOSS
// reasoning: The function F and lemma Test have names that provide no indication of their purpose, and their specifications give no interpretable context.
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Id(==)

function F(s: set<Id>): int

lemma Test(x: Id)
{}




// Tossed File 5:
// filename: MIEIC_mfes_tmp_tmpq3ho7nve_exams_appeal_20_p4.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/MIEIC_mfes_tmp_tmpq3ho7nve_exams_appeal_20_p4.dfy
// keepToss: TOSS
// reasoning: The function name "F" and method name "calcF" provide no interpretable meaning for what they are supposed to compute.
function F(n: nat): nat {}

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{}



// Tossed File 6:
// filename: Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_mod2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_mod2.dfy
// keepToss: TOSS
// reasoning: The function name "f2" provides no indication of its purpose, and there's no specification to clarify what it should compute.

ghost function f2(n: nat): nat {}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{}



// Tossed File 7:
// filename: Metodos_Formais_tmp_tmpbez22nnn_Aula_4_ex3.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Metodos_Formais_tmp_tmpbez22nnn_Aula_4_ex3.dfy
// keepToss: TOSS
// reasoning: The methods Fib and ComputeFib appear to be about Fibonacci numbers which is interpretable, but method Teste has no specification and the name gives no indication of its purpose.
function Fib(n:nat):nat
{}

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{}

method Teste()
{}



// Tossed File 8:
// filename: dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_InSetComprehension.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_InSetComprehension.dfy
// keepToss: TOSS
// reasoning: The lemma names "Tests" and "TestsWhereTriggersMatter" don't indicate what they're testing, and the specifications appear to be arbitrary constraints rather than meaningful functionality.
// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures !z
{}

lemma TestsWhereTriggersMatter<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures z
{}

function Id<T>(t: T): T { t }
predicate Even(x: int) { x % 2 == 0 }

class Container<T> {
  ghost var Contents: set<T>
  var elems: seq<T>

  method Add(t: T)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {}
}

class IntContainer {
  ghost var Contents: set<int>
  var elems: seq<int>

  method Add(t: int)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {}
}

method UnboxedBoundVariables(si: seq<int>)
{}





// Tossed File 9:
// filename: ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old.dfy
// keepToss: TOSS
// reasoning: The method name "m" provides no indication of what the method is supposed to do, and the specification only gives preconditions without any postconditions to clarify the purpose.
class A {

  var value: int

  method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
  {}
}




// Tossed File 10:
// filename: Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy
// keepToss: TOSS
// reasoning: The methods have unclear names like "Quotient" and "Quotient1" with no specifications, making their purposes not reasonably interpretable.
method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{}


method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{}


method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{}


method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{}


method Quotient()
{}

method Quotient1() 
{}



// Tossed File 11:
// filename: circular-queue-implemetation_tmp_tmpnulfdc9l_Queue.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/circular-queue-implemetation_tmp_tmpnulfdc9l_Queue.dfy
// keepToss: TOSS
// reasoning: The code is written primarily in Portuguese (comments like "// Atributos", "// cauda", "// head", "// Abstração", etc.) making it not interpretable for English-only evaluation.
class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {} //[tam] ; [1, 2, 3, 4]

  method insert(item: int)
    // requires rear <= circularQueue.Length
    // ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == [item] &&
    //       |Content| == 1
    //     )
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
    {}

  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {}

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  // {}

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1

  method auxInsertInitQueue(item:int)

  method auxInsertBetweenQueue(item:int)

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
  method remove() returns (item: int)
    requires front < circularQueue.Length
    requires circularQueue.Length > 0
    ensures rear <= |old(Content)|
    ensures circularQueue.Length > 0
    ensures item == old(Content)[old(front)]
    ensures front == (old(front) + 1) % circularQueue.Length
    ensures old(front) < rear ==> Content == old(Content)[old(front)..rear]
    ensures old(front) > rear ==> Content == old(Content)[0 .. rear] + old(Content)[old(front)..|old(Content)|]
  /*{}*/

  method size() returns (size:nat)
    ensures size == counter
  {}

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> counter == 0;
    ensures isEmpty == false ==> counter != 0;
  {}

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
  {}

  // TODO
  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {}
}

method Main ()
{}



// Tossed File 12:
// filename: groupTheory_tmp_tmppmmxvu8h_tutorial2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/groupTheory_tmp_tmppmmxvu8h_tutorial2.dfy
// keepToss: TOSS
// reasoning: The methods M1 and M2 have no specification or context to indicate their purpose.
ghost method M1()
{}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
	requires C == A*B
	ensures C <= A && C <= B
{}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
	requires C == A+B
	ensures A <= C && B <= C
{}

const s0 := {3,8,1}
//var s2 := {4,5}

lemma M2()
{}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
	requires A == {}
	ensures A <= B // same as writing: B >= A
{}

lemma AnySetIsASubsetOfItself(A: set)
	ensures A <= A
{}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
	requires C == A*B && D == A+B
	ensures C <= D
{}




// Tossed File 13:
// filename: Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p5.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p5.dfy
// keepToss: TOSS
// reasoning: The function f has no specification and the method problem5 ensures it returns f(n), but we cannot determine what f is supposed to compute from its name or empty body.
// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {}

method problem5(n:nat) returns (x: int)
ensures x == f(n)
{}



// Tossed File 14:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// keepToss: TOSS
// reasoning: The class Ref has no members or specification, and the method Main has no specification, making their purposes not reasonably interpretable.
// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {}

method Main() {}





// Tossed File 15:
// filename: dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_SeqFromArray.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_SeqFromArray.dfy
// keepToss: TOSS
// reasoning: The method names H, K, L, M, M' provide no interpretable information about their purpose, and the specifications only contain array bounds constraints without indicating what operations these methods are supposed to perform.
// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities

method Main() { }

method H(a: array<int>, c: array<int>, n: nat, j: nat)
  requires j < n == a.Length == c.Length
{}

method K(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length && n <= c.Length
{}

method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
{}

method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{}

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{}




