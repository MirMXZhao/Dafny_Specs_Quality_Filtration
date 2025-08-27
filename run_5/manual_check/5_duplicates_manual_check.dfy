// Kept File 1:
// filename: 285_dafny-training_tmp_tmp_n2kixni_session1_training1.dfy
// filepath: ./run_5/new_filtered/285_dafny-training_tmp_tmp_n2kixni_session1_training1.dfy
// keepToss: KEEP
// duplicateGroup: nan

method abs(x: int) returns (y: int)
    ensures true
{}

method foo(x: int) 
    requires x >= 0
{}

method max(x: int, y: int) returns (m: int)
requires true;
ensures true;
{}

method ex1(n: int)
    requires true
    ensures true
{}

method foo2() 
    ensures false
    decreases *
{}

method find(a: seq<int>, key: int) returns (index: int)
    requires true
    ensures true
{}

method isPalindrome(a: seq<char>) returns (b: bool) 
{
    return true;
}

predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures true
{
  return a;
}
// Kept File 2:
// filename: 445_formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex6.dfy
// filepath: ./run_5/new_filtered/445_formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex6.dfy
// keepToss: KEEP
// duplicateGroup: nan

function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{}

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{}

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}

method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{}
// Kept File 3:
// filename: 65_CSC8204-Dafny_tmp_tmp11yhjb53_stack.dfy
// filepath: ./run_5/new_filtered/65_CSC8204-Dafny_tmp_tmp11yhjb53_stack.dfy
// keepToss: KEEP
// duplicateGroup: nan

type intStack = seq<int>

function isEmpty(s: intStack): bool
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}
// Kept File 4:
// filename: 182_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ReverseString.dfy
// filepath: ./run_5/new_filtered/182_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ReverseString.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate reversed (arr : array<char>, outarr: array<char>)
requires arr != null && outarr != null
requires arr.Length == outarr.Length
reads arr, outarr
{}

method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
{}
// Kept File 5:
// filename: 437_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue40.dfy
// filepath: ./run_5/new_filtered/437_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue40.dfy
// keepToss: KEEP
// duplicateGroup: nan

function SeqRepeat<T>(count:nat, elt:T) : seq<T>
    ensures |SeqRepeat<T>(count, elt)| == count
    ensures forall i :: 0 <= i < count ==> SeqRepeat<T>(count, elt)[i] == elt

datatype Maybe<T> = Nothing | Just(v: T)
type Num = x | 0 <= x < 10
datatype D = C(seq<Maybe<Num>>)
// Kept File 6:
// filename: 298_stunning-palm-tree_tmp_tmpr84c2iwh_ch8.dfy
// filepath: ./run_5/new_filtered/298_stunning-palm-tree_tmp_tmpr84c2iwh_ch8.dfy
// keepToss: KEEP
// duplicateGroup: nan

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{}

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{}

ghost predicate Ordered(xs: List<int>) {
    match xs
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(hd0, Cons(hd1, _)) => (hd0 <= hd1) && Ordered(xs.tail)
}

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{}

ghost function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{}

ghost function Project<T(==)>(xs: List<T>, p: T): List<T> {}

lemma {:induction false} CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  requires Project(xs, p) == Project(ys, p)
  ensures Count(xs, p) == Count(ys, p)
{}

function InsertionSort(xs: List<int>): List<int>
{}

function Insert(x: int, xs: List<int>): List<int>
{}

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{}
// Kept File 7:
// filename: 605_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers.dfy
// filepath: ./run_5/new_filtered/605_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers.dfy
// keepToss: KEEP
// duplicateGroup: nan

module SetHelpers {

    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
        decreases y 
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
        decreases k
    {}

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {}
    
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
        decreases y 
    {}

    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1
        requires |y| >= 2 * |z| / 3 + 1
        ensures |x * y| >= |z| / 3 + 1
    {} 

}
// Kept File 8:
// filename: 25_dafny-synthesis_task_id_69.dfy
// filepath: ./run_5/new_filtered/25_dafny-synthesis_task_id_69.dfy
// keepToss: KEEP
// duplicateGroup: nan

method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
{}
// Kept File 9:
// filename: 171_Clover_abs.dfy
// filepath: ./run_5/new_filtered/171_Clover_abs.dfy
// keepToss: KEEP
// duplicateGroup: nan

method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{}
// Kept File 10:
// filename: 396_Clover_test_array.dfy
// filepath: ./run_5/new_filtered/396_Clover_test_array.dfy
// keepToss: KEEP
// duplicateGroup: nan

method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
{
  a[j] := 60;
}
// Kept File 11:
// filename: 235_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_MatrixMultiplication.dfy
// filepath: ./run_5/new_filtered/235_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_MatrixMultiplication.dfy
// keepToss: KEEP
// duplicateGroup: nan

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
// filename: 31_Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout2.dfy
// filepath: ./run_5/new_filtered/31_Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout2.dfy
// keepToss: KEEP
// duplicateGroup: nan

datatype List<T> = Nil | Cons(head:T,tail:List<T>)
datatype Option<T> = None | Some(elem:T)

ghost function mem<T>(x:T,l:List<T>) : bool {}

ghost function length<T>(l:List<T>) : int {}

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  ensures match list_find(k,l) {}
  decreases l
{}

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  decreases l
  ensures forall k',v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{}


class Hashtable<K(==,!new),V(!new)> {
  var size : int
  var data : array<List<(K,V)>>

  ghost var Repr : set<object>
  ghost var elems : map<K,Option<V>>

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && data in Repr && data.Length > 0 &&
    (forall i :: 0 <= i < data.Length ==> valid_hash(data, i)) &&
    (forall k,v :: valid_data(k,v,elems,data))
  }

  ghost predicate valid_hash(data: array<List<(K,V)>>, i: int)
    requires 0 <= i < data.Length
    reads data
  {}

  ghost predicate valid_data(k: K,v: V,elems: map<K, Option<V>>, data: array<List<(K,V)>>)
    reads this, Repr, data
    requires data.Length > 0
  {}

  function hash(key:K) : int
    ensures hash(key) >= 0

  function bucket(k: K, n: int) : int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  constructor(n:int)
    requires n > 0
    ensures RepInv()
    ensures fresh(Repr-{this})
    ensures elems == map[]
    ensures size == 0
  {}

  method clear()
    requires RepInv()
    ensures RepInv()
    ensures elems == map[]
    ensures fresh(Repr - old(Repr))
    modifies Repr
  {}

  method resize()
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures forall key :: key in old(elems) ==> key in elems
    ensures forall k,v :: k in old(elems) && old(elems)[k] == Some(v) ==> k in elems && elems[k] == Some(v)
    modifies Repr
  {}

  method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>,i: int, oldSize: int, newSize: int)
    requires newData != data
    requires 0 < oldSize == data.Length
    requires newData.Length == 2 * oldSize == newSize
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,newData)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), l) || mem((k,v),newData[bucket(k, newSize)]))
                           else
                             !mem((k,v),newData[bucket(k, newSize)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v ::
              (if 0 <= bucket(k, oldSize) <= i then
                valid_data(k,v,elems,newData)
              else
                !mem((k,v),newData[bucket(k, newSize)]))
    modifies newData
    decreases l
  {}

  method find(k: K) returns (r: Option<V>)
    requires RepInv()
    ensures RepInv()
    ensures match r
            case None => (k !in elems || (k in elems && elems[k] == None))
            case Some(v) => (k in elems && elems[k] == Some(v))
  {}

  method remove(k: K)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k !in elems || elems[k] == None
    ensures forall key :: key != k && key in old(elems) ==> key in elems && elems[key] == old(elems[key])
    modifies Repr
  {}

  method add(k:K,v:V)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k in elems && elems[k] == Some(v)
    ensures forall key :: key != k && key in old(elems) ==> key in elems
    modifies Repr
  {}

}
// Kept File 13:
// filename: 413_Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question6.dfy
// filepath: ./run_5/new_filtered/413_Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question6.dfy
// keepToss: KEEP
// duplicateGroup: nan

method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{}
// Kept File 14:
// filename: 515_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_pregel algorithms_skeleton_nondet-permutation.dfy
// filepath: ./run_5/new_filtered/515_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_pregel algorithms_skeleton_nondet-permutation.dfy
// keepToss: KEEP
// duplicateGroup: nan

module Permutation
{
	method Generate(n: int) returns (perm: array<int>)
		requires n >= 0
		ensures perm != null
		ensures perm.Length == n
		ensures fresh(perm)
		ensures isValid(perm, n)
	{}

	predicate isValid(a: array<int>, n: nat)
		requires a != null && a.Length == n
		reads a
	{}

	predicate distinct(a: array<int>)
		requires a != null
		reads a
	{}

	predicate distinct'(a: array<int>, n: int)
		requires a != null
		requires a.Length >= n
		reads a
	{}

	lemma CardinalityLemma (size: int, s: set<int>)
		requires size >= 0
		requires s == set x | 0 <= x < size
		ensures	size == |s|
	{}

	lemma CardinalityOrderingLemma<T> (s1: set<T>, s2: set<T>)
		requires s1 < s2
		ensures |s1| < |s2|
	{}

	lemma SetDiffLemma<T> (s1: set<T>, s2: set<T>)
		requires s1 < s2
		ensures s2 - s1 != {}
	{}
}
// Kept File 15:
// filename: 417_dafny-synthesis_task_id_142.dfy
// filepath: ./run_5/new_filtered/417_dafny-synthesis_task_id_142.dfy
// keepToss: KEEP
// duplicateGroup: nan

method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{}
// Tossed File 1:
// filename: 419_dafny-synthesis_task_id_618.dfy
// filepath: ./run_5/new_filtered/419_dafny-synthesis_task_id_618.dfy
// keepToss: TOSS
// duplicateGroup: 50.0
method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{}


// Tossed File 2:
// filename: 258_dafny-synthesis_task_id_605.dfy
// filepath: ./run_5/new_filtered/258_dafny-synthesis_task_id_605.dfy
// keepToss: TOSS
// duplicateGroup: 74.0
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{}


// Tossed File 3:
// filename: 33_HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Two Sum_two_sum.dfy
// filepath: ./run_5/new_filtered/33_HATRA-2022-Paper_tmp_tmp5texxy8l_copilot_verification_Two Sum_two_sum.dfy
// keepToss: TOSS
// duplicateGroup: 1.0
method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{}


// Tossed File 4:
// filename: 416_dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_find.dfy
// filepath: ./run_5/new_filtered/416_dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_find.dfy
// keepToss: TOSS
// duplicateGroup: 47.0
method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;
   ensures 0 <= i ==> (i < a.Length && 
                       a[i] == key && 
                       forall k :: 0 <= k < i ==> a[k] != key
                      );
   ensures i < 0 ==> 
           forall k :: 0 <= k < a.Length ==> a[k] != key;
{}


// Tossed File 5:
// filename: 452_dafny-synthesis_task_id_579.dfy
// filepath: ./run_5/new_filtered/452_dafny-synthesis_task_id_579.dfy
// keepToss: TOSS
// duplicateGroup: 57.0
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}


// Tossed File 6:
// filename: 392_Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim.dfy
// filepath: ./run_5/new_filtered/392_Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim.dfy
// keepToss: TOSS
// duplicateGroup: 44.0
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{}

method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
{}

ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{}


// Tossed File 7:
// filename: 305_MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_10_find.dfy
// filepath: ./run_5/new_filtered/305_MFES_2021_tmp_tmpuljn8zd9_FCUL_Exercises_10_find.dfy
// keepToss: TOSS
// duplicateGroup: 47.0
method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
{}


// Tossed File 8:
// filename: 197_formal-verification_tmp_tmpoepcssay_strings3.dfy
// filepath: ./run_5/new_filtered/197_formal-verification_tmp_tmpoepcssay_strings3.dfy
// keepToss: TOSS
// duplicateGroup: 9.0
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
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str)
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
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2)
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{}


// Tossed File 9:
// filename: 106_llm-verified-eval_tmp_tmpd2deqn_i_dafny_3.dfy
// filepath: ./run_5/new_filtered/106_llm-verified-eval_tmp_tmpd2deqn_i_dafny_3.dfy
// keepToss: TOSS
// duplicateGroup: 14.0
function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{}


// Tossed File 10:
// filename: 422_dafny-synthesis_task_id_426.dfy
// filepath: ./run_5/new_filtered/422_dafny-synthesis_task_id_426.dfy
// keepToss: TOSS
// duplicateGroup: 51.0
predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{}


// Tossed File 11:
// filename: 380_Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3.dfy
// filepath: ./run_5/new_filtered/380_Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3.dfy
// keepToss: TOSS
// duplicateGroup: 41.0
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
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{}


// Tossed File 12:
// filename: 85_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Insertion_Sort_Normal.dfy
// filepath: ./run_5/new_filtered/85_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Insertion_Sort_Normal.dfy
// keepToss: TOSS
// duplicateGroup: 23.0
predicate sorted (a: array<int>)
	reads a
{}

predicate sortedA (a: array<int>, i: int)
	requires 0 <= i <= a.Length
	reads a
{}

method lookForMin (a: array<int>, i: int) returns (m: int)
	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{}

method insertionSort (a: array<int>)
	modifies a
	ensures sorted(a)
{}


// Tossed File 13:
// filename: 276_dafny-synthesis_task_id_161.dfy
// filepath: ./run_5/new_filtered/276_dafny-synthesis_task_id_161.dfy
// keepToss: TOSS
// duplicateGroup: 21.0
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}


// Tossed File 14:
// filename: 194_Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBubbleSort.dfy
// filepath: ./run_5/new_filtered/194_Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBubbleSort.dfy
// keepToss: TOSS
// duplicateGroup: 63.0
predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j <= a.Length
reads a
{}

method bubbleSorta(a:array<int>, c:int, f:int)
modifies a 
requires 0 <= c <= f <= a.Length
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{}

method bubbleSort(a:array<int>, c:int, f:int)
modifies a 
requires 0 <= c <= f <= a.Length
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{}


// Tossed File 15:
// filename: 332_dafny-programs_tmp_tmpcwodh6qh_src_max.dfy
// filepath: ./run_5/new_filtered/332_dafny-programs_tmp_tmpcwodh6qh_src_max.dfy
// keepToss: TOSS
// duplicateGroup: 54.0
method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{}

function max(a: int, b: int): int
{}


