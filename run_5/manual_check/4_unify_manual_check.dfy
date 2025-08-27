// Kept File 1:
// filename: 279_dafny-synthesis_task_id_798.dfy
// filepath: ./run_5/new_filtered/279_dafny-synthesis_task_id_798.dfy
// keepToss: KEEP

function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{}

method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
{}
// Kept File 2:
// filename: 355_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram.dfy
// filepath: ./run_5/new_filtered/355_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram.dfy
// keepToss: KEEP

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}
// Kept File 3:
// filename: 160_SENG2011_tmp_tmpgk5jq85q_flex_ex1.dfy
// filepath: ./run_5/new_filtered/160_SENG2011_tmp_tmpgk5jq85q_flex_ex1.dfy
// keepToss: KEEP

function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{}

method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{}
// Kept File 4:
// filename: 449_formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex7.dfy
// filepath: ./run_5/new_filtered/449_formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex7.dfy
// keepToss: KEEP

datatype Bases = A | C | G | T

method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{}

predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
{}
// Kept File 5:
// filename: 576_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort.dfy
// filepath: ./run_5/new_filtered/576_feup-mfes_tmp_tmp6_a1y5a5_examples_SelectionSort.dfy
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
// Kept File 6:
// filename: 183_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise6_Binary_Search.dfy
// filepath: ./run_5/new_filtered/183_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise6_Binary_Search.dfy
// keepToss: KEEP

method binarySearch(a:array<int>, val:int) returns (pos:int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures 0 <= pos < a.Length ==> a[pos] == val
  ensures pos < 0 || pos >= a.Length  ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{}
// Kept File 7:
// filename: 3_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./run_5/new_filtered/3_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// keepToss: KEEP

module Utils {
  class Assertions<T> {
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual

    static method {:extern} expectEquals(expected : T, actual : T)
    ensures expected == actual

    static method {:extern} assertTrue(condition : bool)
    requires condition

    static method {:extern} expectTrue(condition : bool)
    ensures condition
    
    static method {:extern} assertFalse(condition : bool)
    requires !condition

    static method {:extern} expectFalse(condition : bool)
    ensures !condition
  }
}
// Kept File 8:
// filename: 375_Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock.dfy
// filepath: ./run_5/new_filtered/375_Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock.dfy
// keepToss: KEEP

method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
    requires 1 <= prices.Length <= 100000
    requires forall i :: 0 <= i < prices.Length ==> 0 <= prices[i] <= 10000
    ensures forall i, j :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
{}
// Kept File 9:
// filename: 499_Clover_swap.dfy
// filepath: ./run_5/new_filtered/499_Clover_swap.dfy
// keepToss: KEEP

method Swap(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
{}
// Kept File 10:
// filename: 498_dafny-exercises_tmp_tmp5mvrowrx_paper_krml190.dfy
// filepath: ./run_5/new_filtered/498_dafny-exercises_tmp_tmp5mvrowrx_paper_krml190.dfy
// keepToss: KEEP

class Data { }

class Node {
  var list: seq<Data>;
  var footprint: set<Node>;

  var data: Data;
  var next: Node?;

  function Valid(): bool
    reads this, footprint
  {}

  constructor(d: Data)
    ensures Valid() && fresh(footprint - {this})
    ensures list == [d]
  {}

  method SkipHead() returns (r: Node?)
    requires Valid()
    ensures r == null ==> |list| == 1
    ensures r != null ==> r.Valid() && r.footprint <= footprint
  {}

  method Prepend(d: Data) returns (r: Node)
    requires Valid()
    ensures r.Valid() && fresh(r.footprint - old(footprint))
    ensures r.list == [d] + list
  {}

  method ReverseInPlace() returns (reverse: Node)
    requires Valid()
    modifies footprint
    ensures reverse.Valid()
    ensures fresh(reverse.footprint - old(footprint))
    ensures |reverse.list| == |old(list)|
    ensures forall i | 0 <= i < |old(list)| :: old(list)[i] == reverse.list[|old(list)| - 1 - i]
  {}
}
// Kept File 11:
// filename: 2_Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// filepath: ./run_5/new_filtered/2_Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// keepToss: KEEP

method mroot1(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


method mroot2(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

method mroot3(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}
// Kept File 12:
// filename: 112_Clover_convert_map_key.dfy
// filepath: ./run_5/new_filtered/112_Clover_convert_map_key.dfy
// keepToss: KEEP

method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{}
// Kept File 13:
// filename: 56_AssertivePrograming_tmp_tmpwf43uz0e_MergeSort.dfy
// filepath: ./run_5/new_filtered/56_AssertivePrograming_tmp_tmpwf43uz0e_MergeSort.dfy
// keepToss: KEEP

predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{} 

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{}

method {:verify true} MergeLoop(b: array<int>, c: array<int>, d: array<int>,i0: nat , j0: nat)  returns (i: nat, j: nat)
		requires b != c && b != d && b.Length == c.Length + d.Length
		requires Sorted(c[..]) && Sorted(d[..])
		requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
		requires InvSubSet(b[..],c[..],d[..],i0,j0)
		requires InvSorted(b[..],c[..],d[..],i0,j0)
		requires i0 + j0 < b.Length

		modifies b

		ensures i <= c.Length && j <= d.Length && i + j <= b.Length
		ensures InvSubSet(b[..],c[..],d[..],i,j)
		ensures InvSorted(b[..],c[..],d[..],i,j)
		ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
		{}

ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
	i <= |c| && j <= |d| && i + j <= |b| &&
	((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
	((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
	Sorted(b[..i+j])
	}

ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
	i <= |c| && j <= |d| && i + j <= |b| &&
	multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

lemma LemmaMultysetsEquals (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i == |c|;
	requires j == |d|;
	requires i + j == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	ensures multiset(b[..]) == multiset(c[..])+multiset(d[..]);
	{}

lemma lemmaInvSubsetTakeValueFromC (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i < |c|;
	requires j <= |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == c[i]
	ensures multiset(b[..i+j+1]) == multiset(c[..i+1])+multiset(d[..j])
	{}

lemma{:verify true} lemmaInvSubsetTakeValueFromD (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i <= |c|;
	requires j < |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == d[j]
	ensures multiset(b[..i+j+1]) == multiset(c[..i])+multiset(d[..j+1])
	{}
// Kept File 14:
// filename: 404_FlexWeek_tmp_tmpc_tfdj_3_reverse.dfy
// filepath: ./run_5/new_filtered/404_FlexWeek_tmp_tmpc_tfdj_3_reverse.dfy
// keepToss: KEEP

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
{}
// Kept File 15:
// filename: 267_MFS_tmp_tmpmmnu354t_Testes anteriores_T2_ex5_2020_2.dfy
// filepath: ./run_5/new_filtered/267_MFS_tmp_tmpmmnu354t_Testes anteriores_T2_ex5_2020_2.dfy
// keepToss: KEEP

method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{}
