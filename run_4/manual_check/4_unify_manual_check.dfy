// Kept File 1:
// filename: 23_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// filepath: ./run_4/new_filtered/23_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// keepToss: KEEP

module SetHelpers {

    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
    {}

    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {}

    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
    {}

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {}
    
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
    {}

    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1
        requires |y| >= 2 * |z| / 3 + 1
        ensures |x * y| >= |z| / 3 + 1
    {} 

}
// Kept File 2:
// filename: 15_CVS-handout1_tmp_tmptm52no3k_2_no_hints.dfy
// filepath: ./run_4/new_filtered/15_CVS-handout1_tmp_tmptm52no3k_2_no_hints.dfy
// keepToss: KEEP

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{}

predicate mem<T(==)> (l: List<T>, x: T)
{}

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{}
// Kept File 3:
// filename: 21_Clover_rotate_no_hints.dfy
// filepath: ./run_4/new_filtered/21_Clover_rotate_no_hints.dfy
// keepToss: KEEP

method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
{}
// Kept File 4:
// filename: 31_iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// filepath: ./run_4/new_filtered/31_iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// keepToss: KEEP

abstract module ShardedStateMachine {

  type Shard

  predicate valid_shard(a: Shard)

  function glue(a: Shard, b: Shard) : Shard

  lemma glue_commutative(a: Shard, b: Shard)
  ensures glue(a, b) == glue(b, a)

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
  ensures glue(glue(a, b), c) == glue(a, glue(b, c))

  function unit() : Shard
  ensures valid_shard(unit())

  lemma glue_unit(a: Shard)
  ensures glue(a, unit()) == a

  predicate Inv(s: Shard)

  predicate Next(shard: Shard, shard': Shard)

  lemma NextPreservesValid(s: Shard, s': Shard)
  requires valid_shard(s)
  requires Next(s, s')
  ensures valid_shard(s')

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
  requires Next(s, s')
  requires valid_shard(glue(s, t))
  requires Next(glue(s, t), glue(s', t))

  lemma NextPreservesInv(s: Shard, s': Shard)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
}
// Kept File 5:
// filename: 16_MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// filepath: ./run_4/new_filtered/16_MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_no_hints.dfy
// keepToss: KEEP

function power(x: real, n: nat) : real
{}

method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}
// Kept File 6:
// filename: 25_dafny-synthesis_task_id_732_no_hints.dfy
// filepath: ./run_4/new_filtered/25_dafny-synthesis_task_id_732_no_hints.dfy
// keepToss: KEEP

predicate IsSpaceCommaDot(c: char)
{}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{}
// Kept File 7:
// filename: 22_dafny-synthesis_task_id_262_no_hints.dfy
// filepath: ./run_4/new_filtered/22_dafny-synthesis_task_id_262_no_hints.dfy
// keepToss: KEEP

method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}
// Kept File 8:
// filename: 37_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// filepath: ./run_4/new_filtered/37_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort_no_hints.dfy
// keepToss: KEEP

predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{}

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
// Kept File 9:
// filename: 2_FMSE-2022-2023_tmp_tmp6_x_ba46_Lab1_Lab1_no_hints.dfy
// filepath: ./run_4/new_filtered/2_FMSE-2022-2023_tmp_tmp6_x_ba46_Lab1_Lab1_no_hints.dfy
// keepToss: KEEP

newtype Odd = n : int | IsOddNat(n) witness 1

newtype Even = n : int | IsEvenNat(n) witness 2

newtype int32 = n: int | -2147483648 <= n < 2147483648 witness 3

predicate IsOddNat(x: int) {}

predicate IsEvenNat(x: int) {}

lemma AdditionOfTwoOddsResultsInEven(x: int, y: int) 
    requires IsOddNat(x);
    requires IsOddNat(y);
    ensures IsEvenNat(x + y);
{}

predicate IsPrime(x: int)
    requires x >= 0;
{}

lemma AnyPrimeGreaterThanTwoIsOdd(x : int)
    requires x > 2;
    requires IsPrime(x);
    ensures IsOddNat(x);
{}

function add(x: int32, y: int32): int32 {}

function sub(x: int32, y: int32): int32 {}

function mul(x: int32, y: int32): int32 {}

function div(x: int32, y: int32): int32 
    requires y != 0; 
{}

function mod(x: int32, y: int32): int32
    requires y != 0; 
{}

function abs(x: int32): (r: int32)
    ensures r >= 0;
{}
// Kept File 10:
// filename: 17_SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// filepath: ./run_4/new_filtered/17_SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// keepToss: KEEP

method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}
// Kept File 11:
// filename: 33_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// filepath: ./run_4/new_filtered/33_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// keepToss: KEEP

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}
// Kept File 12:
// filename: 38_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue74_no_hints.dfy
// filepath: ./run_4/new_filtered/38_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue74_no_hints.dfy
// keepToss: KEEP

function{:opaque} f(x:int):int { x }

lemma L()
    ensures forall x:int :: f(x) == x
{}
// Kept File 13:
// filename: 7_dafny-synthesis_task_id_424_no_hints.dfy
// filepath: ./run_4/new_filtered/7_dafny-synthesis_task_id_424_no_hints.dfy
// keepToss: KEEP

method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{}
// Kept File 14:
// filename: 10_dafny-synthesis_task_id_591_no_hints.dfy
// filepath: ./run_4/new_filtered/10_dafny-synthesis_task_id_591_no_hints.dfy
// keepToss: KEEP

method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{}
// Kept File 15:
// filename: 32_Clover_min_of_two_no_hints.dfy
// filepath: ./run_4/new_filtered/32_Clover_min_of_two_no_hints.dfy
// keepToss: KEEP

method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{}
