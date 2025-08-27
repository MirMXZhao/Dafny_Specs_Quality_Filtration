// Kept File 1:
// filename: Clover_rotate_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_rotate_no_hints.dfy
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

method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
{}
// Kept File 2:
// filename: Clover_longest_prefix_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Clover_longest_prefix_no_hints.dfy
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

// Kept File 3:
// filename: veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6_no_hints.dfy
// num_methods: 2
// num_lemmas: 4
// num_classes: 2
// num_functions: 2
// num_predicates: 1
// num_ensures: 10
// num_requires: 35
// num_lines: 135
// num_no_ensures: 0
// num_no_requires: 3
// num_none_either: 0
// keepToss: KEEP

class Process {}

function sum(s : seq<nat>) : nat
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{}

lemma sum0(s : seq<nat>)
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  {}

lemma sum_const(s : seq<nat>, x : nat)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
  {
  }

lemma sum_eq(s1 : seq<nat>, s2 : seq<nat>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  {

  }

lemma sum_exept(s1 : seq<nat>, s2 : seq<nat>, x : nat, j : nat)
requires |s1| == |s2|
requires j < |s1|
requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
requires s1[j] == s2[j] + x
ensures sum(s1) == sum(s2) + x
{}


function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
{}

class MatrixVectorMultiplier
{   

    ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers : array<nat>)
        reads this, y, P, M, leftOvers
    {}


    constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers : array<nat>)
        // Idea here is that we already have a set of processes such that each one is assigned one row.
        // Daphny makes it a ginormous pain in the ass to actually create such a set, so we just assume
        // we already have one.

        //this states that the number of rows and processes are the same, and that there is one process
        //for every row, and that no two processes are the same, nor do any two processes share the same
        //row
        requires (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        requires |processes| == leftOvers.Length 
        requires |processes| == M_.Length0
        requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
        requires (forall p, q :: p in processes && q in processes ==> p != q)
        requires (forall p :: p in processes ==> 0 <= p.row < M_.Length0)

        //initializes process start
        requires (forall p :: p in processes ==> 0 == p.curColumn)
        requires (forall p :: p in processes ==> p.opsLeft == M_.Length1)

        requires (forall i :: 0 <= i < y_.Length ==> y_[i] == 0)
        requires y_.Length == M_.Length0

        requires |x_| == M_.Length1
        requires M_.Length0 > 0
        requires |x_| > 0
        ensures (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        ensures Valid(M_, x_, y_, processes, leftOvers)
    {
        
    }

    method processNext(M: array2<int>, x: seq<int>, y: array<int>, P : set<Process>, leftOvers : array<nat>)
        requires Valid(M, x, y, P, leftOvers)
        requires exists p :: (p in P && p.opsLeft > 0)
        requires sum(leftOvers[..]) > 0
        modifies this, y, P, leftOvers
        requires (forall p, q :: p in P && q in P && p != q ==> p.row != q.row)

        ensures Valid(M, x, y, P, leftOvers)
        ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    {}


}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires |processes| == M.Length0
    requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
    requires (forall p, q :: p in processes && q in processes ==> p != q)
    requires (forall p :: p in processes ==> 0 <= p.row < M.Length0)

    requires (forall p :: p in processes ==> 0 == p.curColumn)
    requires (forall p :: p in processes ==> p.opsLeft == M.Length1)

    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    modifies processes, M, x
{}


// lemma lemma_newProcessNotInSet(process: Process, processes: set<Process>)
//     requires (forall p :: p in processes ==> p.row != process.row)
//     ensures process !in processes
// {
// }

// lemma diffRowMeansDiffProcess(p1: Process, p2: Process)
//     requires p1.row != p2.row
//     ensures p1 != p2
// {
// }


// method createSetProcesses(numRows: nat, numColumns: nat) returns (processes: set<Process>)
//     ensures |processes| == numRows
//     ensures (forall p, q :: p in processes && q in processes ==> p != q)
//     ensures (forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row)
//     ensures (forall p :: p in processes ==> 0 <= p.row < numRows)
//     ensures (forall p :: p in processes ==> 0 == p.curColumn)
//     ensures (forall p :: p in processes ==> p.opsLeft == numColumns)
// {}

// method Main()
// {}


// Kept File 4:
// filename: dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-exercise_tmp_tmpouftptir_prac4_ex2_no_hints.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 4
// num_requires: 0
// num_lines: 15
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

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


// Kept File 5:
// filename: dafny-synthesis_task_id_591_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_591_no_hints.dfy
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

method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}
// Kept File 6:
// filename: dafny-synthesis_task_id_2_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_2_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 2
// num_requires: 0
// num_lines: 10
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}
// Kept File 7:
// filename: dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-duck_tmp_tmplawbgxjo_p6_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 2
// num_requires: 0
// num_lines: 11
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}

// Kept File 8:
// filename: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_no_hints.dfy
// num_methods: 2
// num_lemmas: 2
// num_classes: 0
// num_functions: 2
// num_predicates: 0
// num_ensures: 16
// num_requires: 19
// num_lines: 69
// num_no_ensures: 1
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{}

function Sum(A: array<real>): real
  reads A
{}

method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
{}

// example showing that, with the original postcondition, the answer is non-unique!
method PercentileNonUniqueAnswer() returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0

  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= (p/100.0) * total
  ensures i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total

  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= (p/100.0) * total
  ensures i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total

  ensures i1 != i2
{}


// proof that, with the corrected postcondition, the answer is unique
lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0

  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= (p/100.0) * total
  requires i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= (p/100.0) * total
  requires i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total


  ensures i1 == i2
{}
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right
lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  ensures SumUpto(A, end1) < SumUpto(A, end2)
{}


// Kept File 9:
// filename: eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// num_methods: 0
// num_lemmas: 6
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 7
// num_requires: 10
// num_lines: 117
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

/*
 * Copyright 2021 ConsenSys Software Inc.
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

/**
 *  Provide some folk theorems on sets.
 */
module SetHelpers {

    /**
     *  If a set is included in another one, their intersection
     *  is the smallest one.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  y   A finite set.
     *  @returns    A proof that x <= y implies x * y == x.
     */
    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
    {}

    /**
     *  If x [= {0, ..., k - 1} and y [= {0, .., k - 1}
     *  then x U y has at most k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  y   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x [= {0, ..., k - 1} and y [= {0, .., k - 1}
     *              then |x + y| <=k.
     */
    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {}

    /**
     *  If  x [= {0, ..., k - 1} then x has at most k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x [= {0, ..., k - 1} then |x| <= k.
     */
    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
    {}

    /** 
     *  If x contains all successive elements {0, ..., k-1} then x has k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x = {0, ..., k - 1} then |x| == k.
     */

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {}
    
   /**
    *  If a finite set x is included in a finite set y, then
    *  card(x) <= card(y).
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @returns    A proof that x <= y implies card(x) <= card(y)
    *              in other terms, card(_) is monotonic.
    */
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
    {}

   /**
    *  If two finite sets x and y are included in another one z and
    *  have more than 2/3(|z|) elements, then their intersection has more
    *  then |z|/3 elements.
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @param  z   A finite set.
    *  @returns    A proof that if two finite sets x and y are included in 
    *              another one z and have more than 2/3(|z|) elements, then 
    *              their intersection has more then |z|/3 elements.   
    */
    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |x| 
        requires |y| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |y|
        ensures |x * y| >= |z| / 3 + 1    //    or equivalently 3 * |x * y| < |z| 
    {} 

}


// Kept File 10:
// filename: Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower_no_hints.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 1
// num_requires: 1
// num_lines: 6
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 1
// keepToss: KEEP

function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}

// Kept File 11:
// filename: dafny-synthesis_task_id_733_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_733_no_hints.dfy
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
// Kept File 12:
// filename: dafny-synthesis_task_id_808_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_808_no_hints.dfy
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
// Kept File 13:
// filename: stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// num_methods: 1
// num_lemmas: 7
// num_classes: 0
// num_functions: 6
// num_predicates: 5
// num_ensures: 7
// num_requires: 10
// num_lines: 290
// num_no_ensures: 3
// num_no_requires: 1
// num_none_either: 4
// keepToss: KEEP

// Ch. 10: Datatype Invariants

module PQueue {
    export
        // Impl
        provides PQueue
        provides Empty, IsEmpty, Insert, RemoveMin
        // Spec
        provides Valid, Elements, EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin

    // Implementation
    type PQueue = BraunTree
    datatype BraunTree =
        | Leaf
        | Node(x: int, left: BraunTree, right: BraunTree)

    function Empty(): PQueue {
        Leaf
    }

    predicate IsEmpty(pq: PQueue) {
        pq == Leaf
    }

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) =>
            if y < x then
                Node(y, Insert(right ,x), left)
            else
                Node(x, Insert(right, y), left)
    }

    function RemoveMin(pq: PQueue): (int, PQueue)
      requires Valid(pq) && !IsEmpty(pq)
    {
        var Node(x, left, right) := pq;
        (x, DeleteMin(pq))
    }
    
    function DeleteMin(pq: PQueue): PQueue
      requires IsBalanced(pq) && !IsEmpty(pq)
    {
        // Ex. 10.4: by the IsBalanced property, pq.left is always as large or one node larger
        // than pq.right. Thus pq.left.Leaf? ==> pq.right.leaf?
        if pq.right.Leaf? then
            pq.left
        else if pq.left.x <= pq.right.x then
            Node(pq.left.x, pq.right, DeleteMin(pq.left))
        else
            Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
    }

    function ReplaceRoot(pq: PQueue, r: int): PQueue
        requires !IsEmpty(pq)
    {
        // left is empty or r is smaller than either sub-root
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        then
            // simply replace the root
            Node(r, pq.left, pq.right)
        // right is empty, left has one element
        else if pq.right.Leaf? then
            Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
        // both left/right are non-empty and `r` needs to be inserted deeper in the sub-trees
        else if pq.left.x < pq.right.x then
            // promote left root
            Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
        else
            // promote right root
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
    }

    //////////////////////////////////////////////////////////////
    // Specification exposed to callers
    //////////////////////////////////////////////////////////////

    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) =>
            multiset{x} + Elements(left) + Elements(right)
    }

    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }
    
    //////////////////////////////////////////////////////////////
    // Lemmas
    //////////////////////////////////////////////////////////////

    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left.Leaf? || x <= left.x) &&
            (right.Leaf? || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) =>
            IsBalanced(left) && IsBalanced(right) &&
            var L, R := |Elements(left)|, |Elements(right)|;
            L == R || L == R + 1
    }

    // Ex. 10.2
    lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
      requires IsBinaryHeap(pq) && y in Elements(pq)
      ensures pq.x <= y
    {
        if pq.Node? {
                || y in Elements(pq.left) 
                || y in Elements(pq.right));
            if y == pq.x {
            } else if y in Elements(pq.left) {
                BinaryHeapStoresMin(pq.left, y);
            } else if y in Elements(pq.right) {
                BinaryHeapStoresMin(pq.right, y);
            }
        }
    }

    lemma EmptyCorrect()
      ensures Valid(Empty()) && Elements(Empty()) == multiset{}
    { // unfold Empty()
    }
    
    lemma IsEmptyCorrect(pq: PQueue)
      requires Valid(pq)
      ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    {
        if Elements(pq) == multiset{} {
        }
    }
    
    lemma InsertCorrect(pq: PQueue, y: int)
      requires Valid(pq)
      ensures var pq' := Insert(pq, y);
        Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    {}

    lemma RemoveMinCorrect(pq: PQueue)
      requires Valid(pq)
      requires !IsEmpty(pq)
      ensures var (y, pq') := RemoveMin(pq);
              Elements(pq) == Elements(pq') + multiset{y} &&
              IsMin(y, Elements(pq)) &&
              Valid(pq')
    {
        DeleteMinCorrect(pq);
    }
    
    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} DeleteMinCorrect(pq: PQueue)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := DeleteMin(pq);
        Valid(pq') &&
        Elements(pq') + multiset{pq.x} == Elements(pq) &&
        |Elements(pq')| == |Elements(pq)| - 1
    {
        if pq.left.Leaf? || pq.right.Leaf? {}
        else if pq.left.x <= pq.right.x {
            DeleteMinCorrect(pq.left);
        } else {
            var left, right := ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left);
            var pq' := Node(pq.right.x, left, right);
            
            // Elements post-condition
            calc {
                Elements(pq') + multiset{pq.x};
            ==  // defn Elements
                (multiset{pq.right.x} + Elements(left) + Elements(right)) + multiset{pq.x};
            ==  // multiset left assoc
                ((multiset{pq.right.x} + Elements(left)) + Elements(right)) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.right, pq.left.x);
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(right)) + multiset{pq.x};
            ==  // defn right
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(DeleteMin(pq.left))) + multiset{pq.x};
            ==  // multiset right assoc
                (Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left)))) + multiset{pq.x};
            == { DeleteMinCorrect(pq.left);
                (Elements(pq.right) + (Elements(pq.left))) + multiset{pq.x};
            ==
                multiset{pq.x} + Elements(pq.right) + (Elements(pq.left));
            ==
                Elements(pq);
            }
            
            // Validity
            // Prove IsBinaryHeap(pq')
            // IsBinaryHeap(left) && IsBinaryHeap(right) &&
            DeleteMinCorrect(pq.left);
            ReplaceRootCorrect(pq.right, pq.left.x);
            
            // (left.Leaf? || x <= left.x) &&
            BinaryHeapStoresMin(pq.left, pq.left.x);
            BinaryHeapStoresMin(pq.right, pq.right.x);
            // (right.Leaf? || x <= right.x)
        }
    }

    lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} ReplaceRootCorrect(pq: PQueue, r: int)
      requires Valid(pq) && !IsEmpty(pq)
      ensures var pq' := ReplaceRoot(pq, r);
        Valid(pq') &&
        r in Elements(pq') &&
        |Elements(pq')| == |Elements(pq)| &&
        Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x}
    {
        var pq' := ReplaceRoot(pq, r);
        // Element post-condition
        var left, right := pq'.left, pq'.right;
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        {
            // simply replace the root
        }
        else if pq.right.Leaf? {
            // both left/right are non-empty and `r` needs to be inserted deeper in the sub-trees
        }
        else if pq.left.x < pq.right.x {
            // promote left root
            ReplaceRootCorrect(pq.left, r);
            calc {
                Elements(pq') + multiset{pq.x};
            ==
                (multiset{pq.left.x} + Elements(ReplaceRoot(pq.left, r)) + Elements(pq.right)) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.left, r); }
                (Elements(pq.left) + multiset{r}) + Elements(pq.right) + multiset{pq.x};
            ==
                Elements(pq) + multiset{r};
            }
        }
        else {
            // promote right root
            ReplaceRootCorrect(pq.right, r);
            calc {
                Elements(pq') + multiset{pq.x};
            ==  // defn
                (multiset{pq.right.x} + Elements(pq.left) + Elements(ReplaceRoot(pq.right, r))) + multiset{pq.x};
            ==  // assoc
                (Elements(pq.left) + (Elements(ReplaceRoot(pq.right, r)) + multiset{pq.right.x})) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.right, r); }
                (Elements(pq.left) + multiset{r} + Elements(pq.right)) + multiset{pq.x};
            ==
                Elements(pq) + multiset{r};
            }
        }
    }

    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }

}

// Ex 10.0, 10.1
module PQueueClient {
    import PQ = PQueue

    method Client() {
        var pq := PQ.Empty();
        PQ.EmptyCorrect();
        PQ.InsertCorrect(pq, 1);
        var pq1 := PQ.Insert(pq, 1);

        PQ.InsertCorrect(pq1, 2);
        var pq2 := PQ.Insert(pq1, 2);

        PQ.IsEmptyCorrect(pq2);
        PQ.RemoveMinCorrect(pq2);
        var (m, pq3) := PQ.RemoveMin(pq2);        

        PQ.IsEmptyCorrect(pq3);
        PQ.RemoveMinCorrect(pq3);
        var (n, pq4) := PQ.RemoveMin(pq3);        

        PQ.IsEmptyCorrect(pq4);

    }
}

// Kept File 14:
// filename: dafny-synthesis_task_id_424_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/dafny-synthesis_task_id_424_no_hints.dfy
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

method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{}
// Kept File 15:
// filename: feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// num_methods: 4
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 4
// num_requires: 2
// num_lines: 30
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 2
// keepToss: KEEP

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

// Tossed File 1:
// filename: stunning-palm-tree_tmp_tmpr84c2iwh_ch5_no_hints.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/body_removed/stunning-palm-tree_tmp_tmpr84c2iwh_ch5_no_hints.dfy
// num_methods: 3
// num_lemmas: 16
// num_classes: 0
// num_functions: 11
// num_predicates: 0
// num_ensures: 16
// num_requires: 5
// num_lines: 362
// num_no_ensures: 0
// num_no_requires: 11
// num_none_either: 14
// keepToss: TOSS
function More(x: int): int {}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{}

method ExampleLemmaUse(a: int) {}

// Ex 5.0
method ExampleLemmaUse50(a: int) {}

// Ex 5.1
method ExampleLemmaUse51(a: int) {}

// Ex 5.6
function Ack(m: nat, n: nat): nat {}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{}

// Ex 5.5
function Reduce(m: nat, x: int): int {}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{}

// 5.5.1
lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  if m == 0 {  // trivial
  }
  else {
    calc {
      Reduce(m, x);
    ==  // defn
      Reduce(m / 2, x + 1) - m;
    >= { ReduceLowerBound(m/2, x+1);
      x + 1 - 2 * m;
    >  // arith
      x - 2 * m;
    }
  }
}


// ------------------------------------------------------------------------------
// ----- Expr Eval --------------------------------------------------------------
// ------------------------------------------------------------------------------

// 5.8.0

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat
{
  match e {
    case Const(c) => c
    case Var(s) => if s in env then env[s] else 0
    case Node(op, args) => EvalList(op, args, env)
  }
}

// intro'd in 5.8.1
function Unit(op: Op): nat {
  match op case Add => 0 case Mul => 1
}

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
{
  match args {
    case Nil => Unit(op)
    case Cons(e, tail) =>
      var v0, v1 := Eval(e, env), EvalList(op, tail, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1
  }
}

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_) => e
  case Var(s) => if s == n then Const(c) else e
  case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(head, tail) => Cons(Substitute(head, n, c), SubstituteList(tail, n, c))
}

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
  match e
  case Const(_) => {}
  case Var(s) => {
    calc {
      Eval(Substitute(e, n, c), env);
      Eval(if s == n then Const(c) else e, env);
      if s == n then Eval(Const(c), env) else Eval(e, env);
      if s == n then c else Eval(e, env);
      if s == n then c else Eval(e, env[n := c]);
      if s == n then Eval(e, env[n := c]) else Eval(e, env[n := c]);
      Eval(e, env[n := c]);
    }
  }
  case Node(op, args) => {
    EvalSubstituteListCorrect(op, args, n, c, env);
  }
}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
{
  match args
  case Nil => {}
  case Cons(head, tail) => {
    // Ex 5.15
    calc {
      EvalList(op, SubstituteList(args, n, c), env);
    ==  // defn SubstituteList
      EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
    == // unfold defn EvalList
      EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
    ==
      (match op
       case Add => Eval(Substitute(head, n, c), env) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(Substitute(head, n, c), env) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteCorrect(head, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(head, env[n := c]) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteListCorrect(op, tail, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, tail, env[n := c])
       case Mul => Eval(head, env[n := c]) * EvalList(op, tail, env[n := c]));
    == // fold defn Eval/EvalList
      EvalList(op, args, env[n := c]);
    }
  }
}

// Ex 5.16
lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {}
  case Node(op, args) => {
    match args
    case Nil => {}
    case Cons(head, tail) => { EvalEnv(head, n, env); EvalEnvList(op, tail, n, env); }
  }
}

lemma EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
{
  match es
  case Nil => {}
  case Cons(head, tail) => { EvalEnv(head, n, env); EvalEnvList(op, tail, n, env); }
}

// Ex 5.17
lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {}
  case Node(op, args) => {
    calc {
      Eval(Substitute(e, n, 0), env);
      EvalList(op, SubstituteList(args, n, 0), env);
    == { EvalEnvDefaultList(op, args, n, env); }
      EvalList(op, args, env);
      Eval(e, env);
    }
  }
}

lemma EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { EvalEnvDefault(head, n, env); EvalEnvDefaultList(op, tail, n, env); }
}

// Ex 5.18
lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
{
  match e
  case Const(_) => {}
  case Var(_) => {}
  case Node(op, args) => { SubstituteListIdempotent(args, n, c); }
}

lemma SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { SubstituteIdempotent(head, n, c); SubstituteListIdempotent(tail, n, c); }
}

// 5.8.1
// Optimization is correct

function Optimize(e: Expr): Expr
  // intrinsic
  // ensures forall env: map<string, nat> :: Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? then
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e
}

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? {
    OptimizeAndFilterCorrect(e.args, e.op, env); 
    ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env); 
    // calc {
    //   Eval(Optimize(e), env);
    // == // defn Optimize
    //   Eval(Shorten(e.op, OptimizeAndFilter(e.args, Unit(e.op))), env);
    // == { ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env); }
    //   Eval(Node(e.op, OptimizeAndFilter(e.args, Unit(e.op))), env);
    // == { OptimizeAndFilterCorrect(e.args, e.op, env); }
    //   Eval(e, env);
    // }
  }
}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
  // intrinsic
  // ensures forall op: Op, env: map<string, nat> :: u == Unit(op) ==> Eval(Node(op, OptimizeAndFilter(args, u)), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => Nil
  case Cons(head, tail) =>
    var hd, tl := Optimize(head), OptimizeAndFilter(tail, u);
    if hd == Const(u) then tl else Cons(hd, tl)
}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => {}
  case Cons(head, tail) => {
    OptimizeCorrect(head, env);
    OptimizeAndFilterCorrect(tail, op, env);
    // var hd, tl := Optimize(head), OptimizeAndFilter(tail, Unit(op));
    // var u := Unit(op);
    // if hd == Const(u) {
    //   calc {
    //     Eval(Node(op, OptimizeAndFilter(args, u)), env);
    //   ==
    //     EvalList(op, OptimizeAndFilter(args, u), env);
    //   == { assert OptimizeAndFilter(args, u) == tl; }
    //     EvalList(op, tl, env);
    //   ==
    //     Eval(Node(op, tl), env);
    //   == { EvalListUnitHead(hd, tl, op, env); }
    //     Eval(Node(op, Cons(hd, tl)), env);
    //   == { OptimizeCorrect(head, env); OptimizeAndFilterCorrect(tail, op, env); }
    //     Eval(Node(op, args), env);
    //   }
    // } else {
    //   calc {
    //     Eval(Node(op, OptimizeAndFilter(args, u)), env);
    //   ==
    //     EvalList(op, OptimizeAndFilter(args, u), env);
    //   == { assert OptimizeAndFilter(args, u) == Cons(hd, tl); }
    //     EvalList(op, Cons(hd, tl), env);
    //   ==
    //     Eval(Node(op, Cons(hd, tl)), env);
    //   == { OptimizeCorrect(head, env); OptimizeAndFilterCorrect(tail, op, env); }
    //     Eval(Node(op, args), env);
    //   }
    // }
  }
}

lemma EvalListUnitHead(head: Expr, tail: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(head, env) == Unit(op) ==> EvalList(op, Cons(head, tail), env) == EvalList(op, tail, env)
{
  // Note: verifier can prove the whole lemma with empty body!
  var ehead, etail := Eval(head, env), EvalList(op, tail, env);
  if ehead == Unit(op) {
    match op
    case Add => {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==  // defn EvalList
          ehead + etail;
        == // { assert ehead == Unit(Add); assert Unit(Add) == 0; }
          etail;
        }
    }
    case Mul => {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==  // defn EvalList
          ehead * etail;
        == // { assert ehead == 1; }
          etail;
        }
    }
  }
}

function Shorten(op: Op, args: List<Expr>): Expr {
  match args
  case Nil => Const(Unit(op))
  // shorten the singleton list
  case Cons(head, Nil) => head
  // reduce units from the head
  case _ => Node(op, args)
}

lemma ShortenCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => {}
  case Cons(head, Nil) => {
    calc {
      Eval(Node(op, args), env);
      EvalList(op, Cons(head, Nil), env);
      Eval(head, env);
      /* Eval(Shorten(op, Cons(head, Nil)), env); */
      /* Eval(Shorten(op, args), env); */
    }
  }
  case _ => {}
}



