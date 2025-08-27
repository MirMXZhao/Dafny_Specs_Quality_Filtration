// Kept File 1:
// filename: 203_dafny-synthesis_task_id_577.dfy
// filepath: ./run_5/new_tests/203_dafny-synthesis_task_id_577.dfy
// keepToss: KEEP

function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {}

method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
    {}

////////TESTS////////

method TestFactorialOfLastDigit1() {
  var fact := FactorialOfLastDigit(15);
  assert fact == Factorial(5);
}

method TestFactorialOfLastDigit2() {
  var fact := FactorialOfLastDigit(23);
  assert fact == Factorial(3);
}

// Kept File 2:
// filename: 92_DafnyPrograms_tmp_tmp74_f9k_c_map-multiset-implementation.dfy
// filepath: ./run_5/new_tests/92_DafnyPrograms_tmp_tmp74_f9k_c_map-multiset-implementation.dfy
// keepToss: KEEP

trait MyMultiset {

  ghost predicate Valid()
    reads this

  ghost var theMultiset: multiset<int>

  method Add(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures theMultiset == old(theMultiset) + multiset{elem}
    ensures didChange

  ghost predicate Contains(elem: int)
    reads this
  { elem in theMultiset }

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
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

class MultisetImplementationWithMap extends MyMultiset {

  ghost predicate Valid()
    reads this
  {
    (forall i | i in elements.Keys :: elements[i] > 0) && (theMultiset == A(elements)) && (forall i :: i in elements.Keys <==> Contains(i))
  }

  function A(m: map<int, nat>): (s:multiset<int>)
    ensures (forall i | i in m :: m[i] == A(m)[i]) && (m == map[] <==> A(m) == multiset{}) && (forall i :: i in m <==> i in A(m))

  lemma LemmaReverseA(m: map<int, nat>, s : seq<int>)
    requires (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
    ensures A(m) == multiset(s)

  var elements: map<int, nat>;

  constructor MultisetImplementationWithMap()
    ensures Valid()
    ensures elements == map[]
    ensures theMultiset == multiset{}
  {}

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

  method Remove(elem: int) returns (didChange: bool)
    modifies this
    requires Valid()
    ensures Valid()
    ensures old(Contains(elem)) ==> theMultiset == old(theMultiset) - multiset{elem}
    ensures old(Contains(elem)) ==> didChange
    ensures ! old(Contains(elem)) ==> theMultiset == old(theMultiset)
    ensures ! old(Contains(elem)) ==> ! didChange
    ensures didChange <==> elements != old(elements)
  {}

  method Length() returns (len: int)
    requires Valid()
    ensures len == |theMultiset|
  {}

  method equals(other: MyMultiset) returns (equal?: bool)
    requires Valid()
    requires other.Valid()
    ensures Valid()
    ensures equal? <==> theMultiset == other.theMultiset
  {}

  method getElems() returns (elems: seq<int>)
    requires Valid()
    ensures Valid()
    ensures multiset(elems) == theMultiset
  {}

  method Map2Seq(m: map<int, nat>) returns (s: seq<int>)
    requires forall i | i in m.Keys :: i in m.Keys <==> m[i] > 0
    ensures forall i | i in m.Keys :: multiset(s)[i] == m[i]
    ensures forall i | i in m.Keys :: i in s
    ensures A(m) == multiset(s)
    ensures (forall i | i in m :: m[i] == multiset(s)[i]) && (m == map[] <==> multiset(s) == multiset{})
  {}
}

////////TESTS////////

method TestAdd1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange := ms.Add(5);
  assert didChange == true;
}

method TestAdd2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(3);
  var didChange2 := ms.Add(3);
  assert didChange1 == true;
  assert didChange2 == true;
}

method TestRemove1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(7);
  var didChange2 := ms.Remove(7);
  assert didChange2 == true;
}

method TestRemove2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange := ms.Remove(10);
  assert didChange == false;
}

method TestLength1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(1);
  var didChange2 := ms.Add(2);
  var len := ms.Length();
  assert len == 2;
}

method TestLength2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var len := ms.Length();
  assert len == 0;
}

method TestEquals1() {
  var ms1 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var ms2 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms1.Add(5);
  var didChange2 := ms2.Add(5);
  var equal := ms1.equals(ms2);
  assert equal == true;
}

method TestEquals2() {
  var ms1 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var ms2 := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms1.Add(3);
  var didChange2 := ms2.Add(4);
  var equal := ms1.equals(ms2);
  assert equal == false;
}

method TestGetElems1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var didChange1 := ms.Add(2);
  var didChange2 := ms.Add(3);
  var elems := ms.getElems();
  assert multiset(elems) == multiset{2, 3};
}

method TestGetElems2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var elems := ms.getElems();
  assert multiset(elems) == multiset{};
}

method TestMap2Seq1() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var m := map[1 := 2, 3 := 1];
  var s := ms.Map2Seq(m);
  assert multiset(s) == multiset{1, 1, 3};
}

method TestMap2Seq2() {
  var ms := new MultisetImplementationWithMap.MultisetImplementationWithMap();
  var m := map[];
  var s := ms.Map2Seq(m);
  assert multiset(s) == multiset{};
}

// Kept File 3:
// filename: 133_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Lucas-down.dfy
// filepath: ./run_5/new_tests/133_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Lucas-down.dfy
// keepToss: KEEP

// RUN: %dafny /compile:0 /arith:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate Bit(k: nat, n: nat)
{
  if k == 0 then n % 2 == 1
  else Bit(k-1, n / 2)
}

function BitSet(n: nat): set<nat>
{}

lemma BitSize(i: nat, n: nat)
  requires Bit(i, n)
  ensures i < n
{
}

predicate EVEN(n: nat)
{
  n % 2 == 0
}

function binom(a: nat, b: nat): nat
{}

lemma Lucas_Binary''(a: nat, b: nat)
  ensures binom(a, b) % 2 == if EVEN(a) && !EVEN(b) then 0 else binom(a / 2, b / 2) % 2
{}

function Suc(S: set<nat>): set<nat>
{}

lemma SucElements(S: set<nat>)
  ensures forall x :: x in S <==> (x+1) in Suc(S)
{
}

lemma BitSet_Property(n: nat)
  ensures BitSet(n) - {0} == Suc(BitSet(n / 2))
{}

lemma Lucas_Theorem'(m: nat, n: nat)
  ensures BitSet(m) <= BitSet(n) <==> !EVEN(binom(n, m))
{}

////////TESTS////////

method TestBitSet1() {
  var result := BitSet(5);
  assert result == {0, 2};
}

method TestBitSet2() {
  var result := BitSet(7);
  assert result == {0, 1, 2};
}

method TestBinom1() {
  var result := binom(3, 2);
  assert result == 3;
}

method TestBinom2() {
  var result := binom(4, 2);
  assert result == 6;
}

method TestSuc1() {
  var result := Suc({1, 3, 5});
  assert result == {2, 4, 6};
}

method TestSuc2() {
  var result := Suc({0, 2});
  assert result == {1, 3};
}

// Kept File 4:
// filename: 52_dafny-synthesis_task_id_94.dfy
// filepath: ./run_5/new_tests/52_dafny-synthesis_task_id_94.dfy
// keepToss: KEEP

method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{}

////////TESTS////////

method TestMinSecondValueFirst1() {
  var s := new seq<int>[3];
  s[0] := [1, 5];
  s[1] := [3, 2];
  s[2] := [7, 4];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 3;
}

method TestMinSecondValueFirst2() {
  var s := new seq<int>[2];
  s[0] := [10, 8];
  s[1] := [6, 3];
  var firstOfMinSecond := MinSecondValueFirst(s);
  assert firstOfMinSecond == 6;
}

// Kept File 5:
// filename: 64_dafny_examples_tmp_tmp8qotd4ez_leetcode_0027-remove-element.dfy
// filepath: ./run_5/new_tests/64_dafny_examples_tmp_tmp8qotd4ez_leetcode_0027-remove-element.dfy
// keepToss: KEEP

method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{}

////////TESTS////////

method TestRemoveElement1() {
  var nums := new int[4];
  nums[0], nums[1], nums[2], nums[3] := 3, 2, 2, 3;
  var newLength := RemoveElement(nums, 3);
  assert newLength == 2;
}

method TestRemoveElement2() {
  var nums := new int[8];
  nums[0], nums[1], nums[2], nums[3] := 0, 1, 2, 2;
  nums[4], nums[5], nums[6], nums[7] := 3, 0, 4, 2;
  var newLength := RemoveElement(nums, 2);
  assert newLength == 5;
}

// Kept File 6:
// filename: 368_Dafny_tmp_tmpv_d3qi10_2_min.dfy
// filepath: ./run_5/new_tests/368_Dafny_tmp_tmpv_d3qi10_2_min.dfy
// keepToss: KEEP

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{}

method minMethod(a: int, b: int) returns (c: int)
    ensures c <= a && c <= b
    ensures c == a || c == b
    ensures c == min(a, b)
{}

ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{}

method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
{}

////////TESTS////////

method TestMin1() {
  var result := min(5, 3);
  assert result == 3;
}

method TestMin2() {
  var result := min(-2, 7);
  assert result == -2;
}

method TestMinMethod1() {
  var c := minMethod(10, 15);
  assert c == 10;
}

method TestMinMethod2() {
  var c := minMethod(-5, -8);
  assert c == -8;
}

method TestMinFunction1() {
  var result := minFunction(4, 9);
  assert result == 4;
}

method TestMinFunction2() {
  var result := minFunction(12, 6);
  assert result == 6;
}

method TestMinArray1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  var m := minArray(a);
  assert m == 2;
}

method TestMinArray2() {
  var a := new int[4];
  a[0] := -1;
  a[1] := 3;
  a[2] := -5;
  a[3] := 7;
  var m := minArray(a);
  assert m == -5;
}

// Kept File 7:
// filename: 307_dafny-synthesis_task_id_637.dfy
// filepath: ./run_5/new_tests/307_dafny-synthesis_task_id_637.dfy
// keepToss: KEEP

method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{}

////////TESTS////////

method TestIsBreakEven1() {
  var result := IsBreakEven(100, 100);
  assert result == true;
}

method TestIsBreakEven2() {
  var result := IsBreakEven(50, 75);
  assert result == false;
}

// Kept File 8:
// filename: 548_groupTheory_tmp_tmppmmxvu8h_assignment1.dfy
// filepath: ./run_5/new_tests/548_groupTheory_tmp_tmppmmxvu8h_assignment1.dfy
// keepToss: KEEP

lemma Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(L: bool, R: bool)
	ensures (L <==> R) <==> (L ==> R) && (!L ==> !R)
{} 


lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
	ensures A+(B*C) == (A+B)*(A+C)

		{}







lemma Q3_SetUnionIsAssociative(A: iset, B: iset, C: iset)
	ensures (A + B) + C == A + (B + C)

	{}


	
lemma preparation_for_Q4_SetDifferenceIs_NOT_Associative()
	ensures !forall A: set<int>, B: set<int>, C: set<int> :: (A - B) - C == A - (B - C)
{}

lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
	ensures (A - B) - C != A - (B - C)
	{}

////////TESTS////////

method TestQ1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment1() {
    Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(true, true);
}

method TestQ1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment2() {
    Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(false, true);
}

method TestQ2_DistributivityOfSetUnionOverSetIntersection1() {
    var A := {1, 2};
    var B := {2, 3};
    var C := {3, 4};
    Q2_DistributivityOfSetUnionOverSetIntersection(A, B, C);
}

method TestQ2_DistributivityOfSetUnionOverSetIntersection2() {
    var A := {5};
    var B := {6, 7};
    var C := {7, 8};
    Q2_DistributivityOfSetUnionOverSetIntersection(A, B, C);
}

method TestQ3_SetUnionIsAssociative1() {
    var A := iset{1, 2};
    var B := iset{3, 4};
    var C := iset{5, 6};
    Q3_SetUnionIsAssociative(A, B, C);
}

method TestQ3_SetUnionIsAssociative2() {
    var A := iset{10};
    var B := iset{20, 30};
    var C := iset{40};
    Q3_SetUnionIsAssociative(A, B, C);
}

method TestPreparation_for_Q4_SetDifferenceIs_NOT_Associative1() {
    preparation_for_Q4_SetDifferenceIs_NOT_Associative();
}

method TestPreparation_for_Q4_SetDifferenceIs_NOT_Associative2() {
    preparation_for_Q4_SetDifferenceIs_NOT_Associative();
}

method TestQ4_Evidence_That_SetDifferenceIs_NOT_Associative1() {
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
    assert (A - B) - C != A - (B - C);
}

method TestQ4_Evidence_That_SetDifferenceIs_NOT_Associative2() {
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
    assert (A - B) - C != A - (B - C);
}

// Kept File 9:
// filename: 427_Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week9_lemma.dfy
// filepath: ./run_5/new_tests/427_Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week9_lemma.dfy
// keepToss: KEEP

method AssignmentsToMark(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{}

lemma DivisionLemma(n:int,d:int) 
    requires n > 0 && d>1
    ensures n/d < n


method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{}

lemma CommonElement(a:array<nat>, b:array<nat>)
    requires a.Length> 0 && b.Length > 0 && a[0] == b[0]
    ensures multiset(a[..])  * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
{}

////////TESTS////////

method TestAssignmentsToMark1() {
  var r := AssignmentsToMark(5, 3);
  assert r < 5;
}

method TestAssignmentsToMark2() {
  var r := AssignmentsToMark(10, 2);
  assert r < 10;
}

method TestAssignmentsToMarkOne1() {
  var r := AssignmentsToMarkOne(8, 4);
  assert r < 8;
}

method TestAssignmentsToMarkOne2() {
  var r := AssignmentsToMarkOne(15, 5);
  assert r < 15;
}

// Kept File 10:
// filename: 382_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ArrayMap.dfy
// filepath: ./run_5/new_tests/382_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ArrayMap.dfy
// keepToss: KEEP

method ArrayMap<A>(f: int -> A, a: array<A>)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
{}

////////TESTS////////

method TestArrayMap1() {
  var a := new int[3];
  a[0] := 10; a[1] := 20; a[2] := 30;
  ArrayMap(x => x * 2, a);
  assert a[0] == 0;
  assert a[1] == 2;
  assert a[2] == 4;
}

method TestArrayMap2() {
  var a := new int[2];
  a[0] := 5; a[1] := 15;
  ArrayMap(x => x + 1, a);
  assert a[0] == 1;
  assert a[1] == 2;
}

// Kept File 11:
// filename: 27_CVS-Projto1_tmp_tmpb1o0bu8z_fact.dfy
// filepath: ./run_5/new_tests/27_CVS-Projto1_tmp_tmpb1o0bu8z_fact.dfy
// keepToss: KEEP

function fact (n:nat): nat
 decreases n
{}

function factAcc (n:nat, a:int): int
 decreases n
{}

function factAlt(n:nat):int
{factAcc(n,1)}

lemma factAcc_correct (n:nat, a:int)
 ensures factAcc(n, a) == a*fact(n)
{
}

lemma factAlt_correct (n:nat)
 ensures factAlt(n) == fact(n)
{}

datatype List<T> = Nil | Cons(T, List<T>)

function length<T> (l: List<T>) : nat
decreases l
{}

lemma {:induction false} length_non_neg<T> (l:List<T>)
    ensures length(l) >= 0
{}

function lengthTL<T> (l: List<T>, acc: nat) : nat
{}

lemma {:induction false}lengthTL_aux<T> (l: List<T>, acc: nat)
    ensures lengthTL(l, acc) == acc + length(l)
{}

lemma lengthEq<T> (l: List<T>)
    ensures length(l) == lengthTL(l,0)
{}

////////TESTS////////

method TestFact1() {
  var result := fact(0);
  assert result == 1;
}

method TestFact2() {
  var result := fact(5);
  assert result == 120;
}

method TestFactAcc1() {
  var result := factAcc(0, 1);
  assert result == 1;
}

method TestFactAcc2() {
  var result := factAcc(4, 2);
  assert result == 48;
}

method TestFactAlt1() {
  var result := factAlt(0);
  assert result == 1;
}

method TestFactAlt2() {
  var result := factAlt(3);
  assert result == 6;
}

method TestLength1() {
  var result := length(Nil);
  assert result == 0;
}

method TestLength2() {
  var result := length(Cons(1, Cons(2, Cons(3, Nil))));
  assert result == 3;
}

method TestLengthTL1() {
  var result := lengthTL(Nil, 0);
  assert result == 0;
}

method TestLengthTL2() {
  var result := lengthTL(Cons(1, Cons(2, Nil)), 5);
  assert result == 7;
}

// Kept File 12:
// filename: 176_630-dafny_tmp_tmpz2kokaiq_Solution.dfy
// filepath: ./run_5/new_tests/176_630-dafny_tmp_tmpz2kokaiq_Solution.dfy
// keepToss: KEEP

function sorted(a: array<int>) : bool
    reads a
{}

method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 3, 5, 7;
  var index := BinarySearch(a, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var a := new int[3];
  a[0], a[1], a[2] := 2, 4, 6;
  var index := BinarySearch(a, 3);
  assert index == -1;
}

// Kept File 13:
// filename: 156_Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_IncrementMatrix.dfy
// filepath: ./run_5/new_tests/156_Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_IncrementMatrix.dfy
// keepToss: KEEP

method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{}

////////TESTS////////

method TestIncrementMatrix1() {
  var a := new int[2,2];
  a[0,0] := 1; a[0,1] := 2;
  a[1,0] := 3; a[1,1] := 4;
  var old_a := new int[2,2];
  old_a[0,0] := a[0,0]; old_a[0,1] := a[0,1];
  old_a[1,0] := a[1,0]; old_a[1,1] := a[1,1];
  IncrementMatrix(a);
  assert a[0,0] == old_a[0,0] + 1;
  assert a[0,1] == old_a[0,1] + 1;
  assert a[1,0] == old_a[1,0] + 1;
  assert a[1,1] == old_a[1,1] + 1;
}

method TestIncrementMatrix2() {
  var a := new int[1,3];
  a[0,0] := -5; a[0,1] := 0; a[0,2] := 10;
  var old_a := new int[1,3];
  old_a[0,0] := a[0,0]; old_a[0,1] := a[0,1]; old_a[0,2] := a[0,2];
  IncrementMatrix(a);
  assert a[0,0] == old_a[0,0] + 1;
  assert a[0,1] == old_a[0,1] + 1;
  assert a[0,2] == old_a[0,2] + 1;
}

// Kept File 14:
// filename: 490_vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy
// filepath: ./run_5/new_tests/490_vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy
// keepToss: KEEP

method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q

{}

////////TESTS////////

method TestTorneo1() {
  var Valores := new real[20];
  Valores[0] := 5.0;
  Valores[1] := 3.0;
  Valores[2] := 7.0;
  var pos_padre, pos_madre := torneo(Valores, 0, 1, 2);
  assert pos_padre == 2;
  assert pos_madre == 0;
}

method TestTorneo2() {
  var Valores := new real[25];
  Valores[5] := 2.5;
  Valores[10] := 8.5;
  Valores[15] := 6.0;
  var pos_padre, pos_madre := torneo(Valores, 5, 10, 15);
  assert pos_padre == 10;
  assert pos_madre == 15;
}

// Kept File 15:
// filename: 268_Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3 copy 2.dfy
// filepath: ./run_5/new_tests/268_Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3 copy 2.dfy
// keepToss: KEEP

class TwoStacks<T(0)(==)> 
{
    ghost var s1 :seq<T>
    ghost var s2 :seq<T>
    ghost const N :nat
    ghost var Repr : set<object>
    var data: array<T>
    var n1: nat
    var n2: nat

    ghost predicate Valid()
        reads this,Repr
        ensures Valid() ==> this in Repr &&  |s1| + |s2| <= N && 0 <= |s1| <= N && 0 <=|s2| <= N
    {}

    constructor (N: nat)
        ensures Valid() && fresh(Repr)
        ensures s1 == s2 == [] && this.N == N
    {}
    
    method push1(element:T) returns (FullStatus:bool)
        requires Valid()
        modifies Repr
        ensures old(|s1|) != N && old(|s1|) + old(|s2|) != N ==> s1 ==  old(s1) + [element];
        ensures old(|s1|) == N ==> FullStatus == false
        ensures old(|s1|) != N && old(|s1|) + old(|s2|) == N ==> FullStatus == false
        ensures Valid() && fresh(Repr - old(Repr))
    {} 

    method push2(element:T) returns (FullStatus:bool)
        requires Valid()
        modifies Repr
        ensures old(|s2|) != N && old(|s1|) + old(|s2|) != N ==> s2 ==  old(s2) + [element];
        ensures old(|s2|) == N ==> FullStatus == false
        ensures old(|s2|) != N && old(|s1|) + old(|s2|) == N ==> FullStatus == false
        ensures Valid() && fresh(Repr - old(Repr))
    {} 

    method pop1() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        modifies Repr
        ensures old(|s1|) != 0 ==> s1 == old(s1[0..|s1|-1]) && EmptyStatus == true && PopedItem == old(s1[|s1|-1]) 
        ensures old(|s1|) == 0 ==> EmptyStatus == false 
        ensures Valid() && fresh(Repr - old(Repr))
    {}

    method pop2() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        modifies Repr
        ensures old(|s2|) != 0 ==> s2 == old(s2[0..|s2|-1]) && EmptyStatus == true && PopedItem == old(s2[|s2|-1]) 
        ensures old(|s2|) == 0 ==> EmptyStatus == false 
        ensures Valid() && fresh(Repr - old(Repr))
    {}

    method peek1() returns (EmptyStatus:bool, TopItem:T)
        requires Valid()
        ensures Empty1() ==> EmptyStatus == false
        ensures !Empty1() ==> EmptyStatus == true && TopItem == s1[|s1|-1] 
        ensures Valid()
    {}

    method peek2() returns (EmptyStatus:bool, TopItem:T)
        requires Valid()
        ensures Empty2() ==> EmptyStatus == false
        ensures !Empty2() ==> EmptyStatus == true && TopItem == s2[|s2|-1] 
        ensures Valid()
    {}
    
    ghost predicate Empty1() 
        requires Valid()
        reads this,Repr
        ensures Empty1() ==> |s1| == 0
        ensures Valid()
    {}

    ghost predicate Empty2() 
        reads this
        ensures Empty2() ==> |s2| == 0
    {}
    
    method search1(Element:T) returns (position:int)
        requires Valid()
        ensures position == -1 || position >= 1
        ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element && !Empty1()
        ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element || Empty1()
        ensures Valid()
    {}

    method search3(Element:T) returns (position:int)
        requires Valid()
        ensures position == -1 || position >= 1
        ensures position >= 1 ==> exists i::0 <=i < |s2| && s2[i] == Element && !Empty2()
        ensures Valid()
    {}
}

////////TESTS////////

method TestTwoStacks1() {
    var ts := new TwoStacks<int>(5);
    var fullStatus := ts.push1(10);
    assert fullStatus == true;
    assert ts.s1 == [10];
}

method TestTwoStacks2() {
    var ts := new TwoStacks<int>(1);
    var fullStatus1 := ts.push1(5);
    var fullStatus2 := ts.push1(3);
    assert fullStatus1 == true;
    assert fullStatus2 == false;
}

