// Kept File 1:
// filename: 17_SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// filepath: ./run_4/new_tests/17_SENG2011_tmp_tmpgk5jq85q_ass1_ex8_no_hints.dfy
// keepToss: KEEP

method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
{}

////////TESTS////////

method TestGetEven1() {
  var a := new nat[4] := [1, 3, 5, 7];
  GetEven(a);
  assert a[0] % 2 == 0;
  assert a[1] % 2 == 0;
  assert a[2] % 2 == 0;
  assert a[3] % 2 == 0;
}

method TestGetEven2() {
  var a := new nat[3] := [2, 8, 12];
  GetEven(a);
  assert a[0] % 2 == 0;
  assert a[1] % 2 == 0;
  assert a[2] % 2 == 0;
}

// Kept File 2:
// filename: 35_cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// filepath: ./run_4/new_tests/35_cs245-verification_tmp_tmp0h_nxhqp_SortingIssues_BubbleSortCode_no_hints.dfy
// keepToss: KEEP

method BubbleSort(A: array<int>, n: int)
modifies A;
requires A.Length>=0 && n==A.Length;
{}

////////TESTS////////

method TestBubbleSort1() {
  var A := new int[4];
  A[0] := 3; A[1] := 1; A[2] := 4; A[3] := 2;
  BubbleSort(A, 4);
  assert A[0] == 1 && A[1] == 2 && A[2] == 3 && A[3] == 4;
}

method TestBubbleSort2() {
  var A := new int[3];
  A[0] := 5; A[1] := 5; A[2] := 5;
  BubbleSort(A, 3);
  assert A[0] == 5 && A[1] == 5 && A[2] == 5;
}

// Kept File 3:
// filename: 4_dafny-synthesis_task_id_808_no_hints.dfy
// filepath: ./run_4/new_tests/4_dafny-synthesis_task_id_808_no_hints.dfy
// keepToss: KEEP

method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{}

////////TESTS////////

method TestContainsK1() {
  var s := [1, 2, 3, 4, 5];
  var result := ContainsK(s, 3);
  assert result == true;
}

method TestContainsK2() {
  var s := [1, 2, 4, 5];
  var result := ContainsK(s, 3);
  assert result == false;
}

// Kept File 4:
// filename: 31_iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
// filepath: ./run_4/new_tests/31_iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine_no_hints.dfy
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

////////TESTS////////

method TestShardedStateMachine1() {
  var s := unit();
  var s' := unit();
  assume Next(s, s');
  assume Inv(s);
  NextPreservesInv(s, s');
  assert Inv(s');
}

method TestShardedStateMachine2() {
  var a := unit();
  var b := unit();
  glue_commutative(a, b);
  assert glue(a, b) == glue(b, a);
}

// Kept File 5:
// filename: 12_Clover_two_sum_no_hints.dfy
// filepath: ./run_4/new_tests/12_Clover_two_sum_no_hints.dfy
// keepToss: KEEP

method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{}

////////TESTS////////

method TestTwoSum1() {
  var nums := new int[4];
  nums[0] := 2;
  nums[1] := 7;
  nums[2] := 11;
  nums[3] := 15;
  var i, j := twoSum(nums, 9);
  assert i == 0;
  assert j == 1;
}

method TestTwoSum2() {
  var nums := new int[3];
  nums[0] := 3;
  nums[1] := 2;
  nums[2] := 4;
  var i, j := twoSum(nums, 6);
  assert i == 1;
  assert j == 2;
}

// Kept File 6:
// filename: 33_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// filepath: ./run_4/new_tests/33_Software-Verification_tmp_tmpv4ueky2d_Valid Anagram_valid_anagram_no_hints.dfy
// keepToss: KEEP

method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}

////////TESTS////////

method TestIsAnagram1() {
  var s := "listen";
  var t := "silent";
  var result := is_anagram(s, t);
  assert result == true;
}

method TestIsAnagram2() {
  var s := "hello";
  var t := "world";
  var result := is_anagram(s, t);
  assert result == false;
}

method TestIsEqual1() {
  var s := multiset{'a', 'b', 'c'};
  var t := multiset{'c', 'a', 'b'};
  var result := is_equal(s, t);
  assert result == true;
}

method TestIsEqual2() {
  var s := multiset{'a', 'b'};
  var t := multiset{'a', 'c'};
  var result := is_equal(s, t);
  assert result == false;
}

// Kept File 7:
// filename: 19_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_no_hints.dfy
// filepath: ./run_4/new_tests/19_Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_Percentile_no_hints.dfy
// keepToss: KEEP

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

lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  ensures SumUpto(A, end1) < SumUpto(A, end2)
{}

////////TESTS////////

method TestPercentileNonUniqueAnswer1() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert SumUpto(A, i1) <= (p/100.0) * total;
  assert i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total;
  assert -1 <= i2 < A.Length;
  assert SumUpto(A, i2) <= (p/100.0) * total;
  assert i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total;
  assert i1 != i2;
}

method TestPercentileNonUniqueAnswer2() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert SumUpto(A, i1) <= (p/100.0) * total;
  assert i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total;
  assert -1 <= i2 < A.Length;
  assert SumUpto(A, i2) <= (p/100.0) * total;
  assert i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total;
  assert i1 != i2;
}

// Kept File 8:
// filename: 22_dafny-synthesis_task_id_262_no_hints.dfy
// filepath: ./run_4/new_tests/22_dafny-synthesis_task_id_262_no_hints.dfy
// keepToss: KEEP

method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{}

////////TESTS////////

method TestSplitArray1() {
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 2, 3, 4, 5;
  var firstPart, secondPart := SplitArray(arr, 2);
  assert firstPart == [1, 2];
  assert secondPart == [3, 4, 5];
}

method TestSplitArray2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 10, 20, 30, 40;
  var firstPart, secondPart := SplitArray(arr, 0);
  assert firstPart == [];
  assert secondPart == [10, 20, 30, 40];
}

// Kept File 9:
// filename: 25_dafny-synthesis_task_id_732_no_hints.dfy
// filepath: ./run_4/new_tests/25_dafny-synthesis_task_id_732_no_hints.dfy
// keepToss: KEEP

predicate IsSpaceCommaDot(c: char)
{}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceWithColon1() {
  var s := "hello, world.";
  var v := ReplaceWithColon(s);
  assert v == "hello: world:";
}

method TestReplaceWithColon2() {
  var s := "abc def";
  var v := ReplaceWithColon(s);
  assert v == "abc:def";
}

// Kept File 10:
// filename: 18_Clover_online_max_no_hints.dfy
// filepath: ./run_4/new_tests/18_Clover_online_max_no_hints.dfy
// keepToss: KEEP

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}

////////TESTS////////

method TestOnlineMax1() {
  var a := new int[5];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 1; a[4] := 5;
  var m, p := onlineMax(a, 2);
  assert m == 3;
  assert p == 2;
}

method TestOnlineMax2() {
  var a := new int[4];
  a[0] := 2; a[1] := 5; a[2] := 1; a[3] := 3;
  var m, p := onlineMax(a, 1);
  assert m == 2;
  assert p == 3;
}

// Kept File 11:
// filename: 24_dafny-synthesis_task_id_2_no_hints.dfy
// filepath: ./run_4/new_tests/24_dafny-synthesis_task_id_2_no_hints.dfy
// keepToss: KEEP

predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

////////TESTS////////

method TestSharedElements1() {
  var a := new int[3] [1, 2, 3];
  var b := new int[3] [2, 3, 4];
  var result := SharedElements(a, b);
  assert result == [2, 3];
}

method TestSharedElements2() {
  var a := new int[2] [1, 5];
  var b := new int[2] [6, 7];
  var result := SharedElements(a, b);
  assert result == [];
}

// Kept File 12:
// filename: 38_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue74_no_hints.dfy
// filepath: ./run_4/new_tests/38_dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue74_no_hints.dfy
// keepToss: KEEP

function{:opaque} f(x:int):int { x }

lemma L()
    ensures forall x:int :: f(x) == x
{}

////////TESTS////////

method Testf1() {
  var result := f(5);
  assert result == 5;
}

method Testf2() {
  var result := f(-3);
  assert result == -3;
}

// Kept File 13:
// filename: 23_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// filepath: ./run_4/new_tests/23_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
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

////////TESTS////////

method TestInterSmallest1() {
  var x := {1, 2, 3};
  var y := {1, 2, 3, 4, 5};
  interSmallest(x, y);
  assert x * y == x;
}

method TestInterSmallest2() {
  var x := {};
  var y := {10, 20, 30};
  interSmallest(x, y);
  assert x * y == x;
}

method TestUnionCardBound1() {
  var x := {0, 1, 2};
  var y := {2, 3, 4};
  var k := 5;
  unionCardBound(x, y, k);
  assert forall e :: e in x + y ==> e < k;
  assert |x + y| <= k;
}

method TestUnionCardBound2() {
  var x := {0};
  var y := {1};
  var k := 3;
  unionCardBound(x, y, k);
  assert forall e :: e in x + y ==> e < k;
  assert |x + y| <= k;
}

method TestNatSetCardBound1() {
  var x := {0, 1, 2, 3};
  var k := 5;
  natSetCardBound(x, k);
  assert |x| <= k;
}

method TestNatSetCardBound2() {
  var x := {};
  var k := 10;
  natSetCardBound(x, k);
  assert |x| <= k;
}

method TestSuccessiveNatSetCardBound1() {
  var x := set x: nat | 0 <= x < 3 :: x;
  var k := 3;
  successiveNatSetCardBound(x, k);
  assert |x| == k;
}

method TestSuccessiveNatSetCardBound2() {
  var x := set x: nat | 0 <= x < 0 :: x;
  var k := 0;
  successiveNatSetCardBound(x, k);
  assert |x| == k;
}

method TestCardIsMonotonic1() {
  var x := {1, 2};
  var y := {1, 2, 3, 4};
  cardIsMonotonic(x, y);
  assert |x| <= |y|;
}

method TestCardIsMonotonic2() {
  var x := {};
  var y := {5, 10, 15};
  cardIsMonotonic(x, y);
  assert |x| <= |y|;
}

method TestPigeonHolePrinciple1() {
  var x := {1, 2, 3, 4, 5};
  var y := {1, 2, 3, 4, 6};
  var z := {1, 2, 3, 4, 5, 6};
  pigeonHolePrinciple(x, y, z);
  assert |x * y| >= |z| / 3 + 1;
}

method TestPigeonHolePrinciple2() {
  var x := {1, 2, 3};
  var y := {2, 3, 4};
  var z := {1, 2, 3, 4};
  pigeonHolePrinciple(x, y, z);
  assert |x * y| >= |z| / 3 + 1;
}

// Kept File 14:
// filename: 32_Clover_min_of_two_no_hints.dfy
// filepath: ./run_4/new_tests/32_Clover_min_of_two_no_hints.dfy
// keepToss: KEEP

method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{}

////////TESTS////////

method TestMin1() {
  var z := Min(3, 7);
  assert z == 3;
}

method TestMin2() {
  var z := Min(9, 4);
  assert z == 4;
}

// Kept File 15:
// filename: 6_stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// filepath: ./run_4/new_tests/6_stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// keepToss: KEEP

module PQueue {
    export
        provides PQueue
        provides Empty, IsEmpty, Insert, RemoveMin
        provides Valid, Elements, EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin

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
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        then
            Node(r, pq.left, pq.right)
        else if pq.right.Leaf? then
            Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
        else if pq.left.x < pq.right.x then
            Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
        else
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
    }

    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) =>
            multiset{x} + Elements(left) + Elements(right)
    }

    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }
    
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
    {
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
            
            calc {
                Elements(pq') + multiset{pq.x};
            ==
                (multiset{pq.right.x} + Elements(left) + Elements(right)) + multiset{pq.x};
            ==
                ((multiset{pq.right.x} + Elements(left)) + Elements(right)) + multiset{pq.x};
            == { ReplaceRootCorrect(pq.right, pq.left.x);
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(right)) + multiset{pq.x};
            ==
                ((Elements(pq.right) + multiset{pq.left.x}) + Elements(DeleteMin(pq.left))) + multiset{pq.x};
            ==
                (Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left)))) + multiset{pq.x};
            == { DeleteMinCorrect(pq.left);
                (Elements(pq.right) + (Elements(pq.left))) + multiset{pq.x};
            ==
                multiset{pq.x} + Elements(pq.right) + (Elements(pq.left));
            ==
                Elements(pq);
            }
            
            DeleteMinCorrect(pq.left);
            ReplaceRootCorrect(pq.right, pq.left.x);
            
            BinaryHeapStoresMin(pq.left, pq.left.x);
            BinaryHeapStoresMin(pq.right, pq.right.x);
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
        var left, right := pq'.left, pq'.right;
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        {
        }
        else if pq.right.Leaf? {
        }
        else if pq.left.x < pq.right.x {
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
            ReplaceRootCorrect(pq.right, r);
            calc {
                Elements(pq') + multiset{pq.x};
            ==
                (multiset{pq.right.x} + Elements(pq.left) + Elements(ReplaceRoot(pq.right, r))) + multiset{pq.x};
            ==
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

////////TESTS////////

method TestRemoveMin1() {
  var pq := PQueue.Node(1, PQueue.Node(3, PQueue.Leaf, PQueue.Leaf), PQueue.Node(2, PQueue.Leaf, PQueue.Leaf));
  var min, pq_new := PQueue.RemoveMin(pq);
  assert min == 1;
  assert pq_new == PQueue.Node(2, PQueue.Node(3, PQueue.Leaf, PQueue.Leaf), PQueue.Leaf);
}

method TestRemoveMin2() {
  var pq := PQueue.Node(5, PQueue.Leaf, PQueue.Leaf);
  var min, pq_new := PQueue.RemoveMin(pq);
  assert min == 5;
  assert pq_new == PQueue.Leaf;
}

