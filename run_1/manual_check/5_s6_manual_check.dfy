// Kept File 1:
// filename: 63_stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
// filepath: ./run_1/new_tests/63_stunning-palm-tree_tmp_tmpr84c2iwh_ch10_no_hints.dfy
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
            (r <= pq.left.x

////////TESTS////////

method TestInsert1() {
    var pq := Node(5, Leaf, Leaf);
    var result := Insert(pq, 3);
    assert result == Node(3, Node(5, Leaf, Leaf), Leaf);
}

method TestInsert2() {
    var pq := Leaf;
    var result := Insert(pq, 7);
    assert result == Node(7, Leaf, Leaf);
}

// Kept File 2:
// filename: 128_Clover_convert_map_key_no_hints.dfy
// filepath: ./run_1/new_tests/128_Clover_convert_map_key_no_hints.dfy
// keepToss: KEEP

method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{}

////////TESTS////////

method TestConvertMapKey1() {
  var inputs := map[1 := true, 2 := false];
  var f := x => x + 10;
  var r := convert_map_key(inputs, f);
  assert r == map[11 := true, 12 := false];
}

method TestConvertMapKey2() {
  var inputs := map[0 := true, 3 := false, 5 := true];
  var f := x => x * 2;
  var r := convert_map_key(inputs, f);
  assert r == map[0 := true, 6 := false, 10 := true];
}

// Kept File 3:
// filename: 185_dafny-synthesis_task_id_431_no_hints.dfy
// filepath: ./run_1/new_tests/185_dafny-synthesis_task_id_431_no_hints.dfy
// keepToss: KEEP

method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{}

////////TESTS////////

method TestHasCommonElement1() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var b := new int[3];
  b[0] := 4;
  b[1] := 2;
  b[2] := 6;
  var result := HasCommonElement(a, b);
  assert result == true;
}

method TestHasCommonElement2() {
  var a := new int[2];
  a[0] := 1;
  a[1] := 3;
  var b := new int[2];
  b[0] := 2;
  b[1] := 4;
  var result := HasCommonElement(a, b);
  assert result == false;
}

// Kept File 4:
// filename: 170_dafny-synthesis_task_id_447_no_hints.dfy
// filepath: ./run_1/new_tests/170_dafny-synthesis_task_id_447_no_hints.dfy
// keepToss: KEEP

method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures cubed.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{}

////////TESTS////////

method TestCubeElements1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var cubed := CubeElements(a);
  assert cubed[0] == 1;
  assert cubed[1] == 8;
  assert cubed[2] == 27;
  assert cubed[3] == 64;
}

method TestCubeElements2() {
  var a := new int[3];
  a[0] := -2; a[1] := 0; a[2] := 5;
  var cubed := CubeElements(a);
  assert cubed[0] == -8;
  assert cubed[1] == 0;
  assert cubed[2] == 125;
}

// Kept File 5:
// filename: 155_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
// filepath: ./run_1/new_tests/155_eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers_no_hints.dfy
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
  var x := {1, 2};
  var y := {1, 2, 3, 4};
  SetHelpers.interSmallest(x, y);
}

method TestInterSmallest2() {
  var x := {};
  var y := {5, 10, 15};
  SetHelpers.interSmallest(x, y);
}

method TestUnionCardBound1() {
  var x := {0, 1, 2};
  var y := {2, 3, 4};
  var k := 5;
  SetHelpers.unionCardBound(x, y, k);
}

method TestUnionCardBound2() {
  var x := {0};
  var y := {1};
  var k := 3;
  SetHelpers.unionCardBound(x, y, k);
}

method TestNatSetCardBound1() {
  var x := {0, 1, 2};
  var k := 5;
  SetHelpers.natSetCardBound(x, k);
}

method TestNatSetCardBound2() {
  var x := {};
  var k := 10;
  SetHelpers.natSetCardBound(x, k);
}

method TestSuccessiveNatSetCardBound1() {
  var x := set x: nat | 0 <= x < 3 :: x;
  var k := 3;
  SetHelpers.successiveNatSetCardBound(x, k);
}

method TestSuccessiveNatSetCardBound2() {
  var x := set x: nat | 0 <= x < 0 :: x;
  var k := 0;
  SetHelpers.successiveNatSetCardBound(x, k);
}

method TestCardIsMonotonic1() {
  var x := {1, 2};
  var y := {1, 2, 3, 4};
  SetHelpers.cardIsMonotonic(

// Kept File 6:
// filename: 74_dafny-synthesis_task_id_743_no_hints.dfy
// filepath: ./run_1/new_tests/74_dafny-synthesis_task_id_743_no_hints.dfy
// keepToss: KEEP

method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{}

////////TESTS////////

method TestRotateRight1() {
  var l := [1, 2, 3, 4, 5];
  var n := 2;
  var r := RotateRight(l, n);
  assert r == [4, 5, 1, 2, 3];
}

method TestRotateRight2() {
  var l := [10, 20, 30];
  var n := 0;
  var r := RotateRight(l, n);
  assert r == [10, 20, 30];
}

// Kept File 7:
// filename: 89_Clover_below_zero_no_hints.dfy
// filepath: ./run_1/new_tests/89_Clover_below_zero_no_hints.dfy
// keepToss: KEEP

method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{}

////////TESTS////////

method TestBelowZero1() {
  var operations := [1, 2, -4, 5];
  var s, result := below_zero(operations);
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == -1;
  assert s[4] == 4;
  assert result == true;
}

method TestBelowZero2() {
  var operations := [2, 1, -1, 3];
  var s, result := below_zero(operations);
  assert s[0] == 0;
  assert s[1] == 2;
  assert s[2] == 3;
  assert s[3] == 2;
  assert s[4] == 5;
  assert result == false;
}

// Kept File 8:
// filename: 51_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_IntegerSet_no_hints.dfy
// filepath: ./run_1/new_tests/51_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_IntegerSet_no_hints.dfy
// keepToss: KEEP

module IntegerSet {

    class Set {

        var elements: seq<int>;

        constructor Set0() 
        ensures this.elements == []
        ensures |this.elements| == 0
        {}

        constructor Set(elements: seq<int>)
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures this.elements == elements
        ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements|  && j != i:: this.elements[i] != this.elements[j]
        {}

        method size() returns (size : int)
        ensures size == |elements|
        {}

        method addElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> elements == old(elements)
        ensures element !in old(elements) ==> |elements| == |old(elements)| + 1 && element in elements && forall i : int :: i in old(elements) ==> i in elements
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {}

        method removeElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> |elements| == |old(elements)| - 1 && (forall i : int :: i in old(elements) && i != element <==> i in elements) && element !in elements
        ensures element !in old(elements) ==> elements == old(elements)
        ensures forall i, j | 0 <=

////////TESTS////////

method testSet01() {
  var s := new Set0();
  var size := s.size();
  assert size == 0;
}

method testSet02() {
  var s := new Set([1, 3, 5]);
  var size := s.size();
  assert size == 3;
}

method testaddElement1() {
  var s := new Set([1, 3]);
  s.addElement(5);
  assert s.elements == [1, 3, 5] || s.elements == [1, 5, 3] || s.elements == [3, 1, 5] || s.elements == [3, 5, 1] || s.elements == [5, 1, 3] || s.elements == [5, 3, 1];
}

method testaddElement2() {
  var s := new Set([1, 3]);
  s.addElement(1);
  assert s.elements == [1, 3];
}

method testremoveElement1() {
  var s := new Set([1, 3, 5]);
  s.removeElement(3);
  assert s.elements == [1, 5] || s.elements == [5, 1];
}

method testremoveElement2() {
  var s := new Set([1, 3, 5]);
  s.removeElement(7);
  assert s.elements == [1, 3, 5];
}

// Kept File 9:
// filename: 114_dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices_no_hints.dfy
// filepath: ./run_1/new_tests/114_dafny-language-server_tmp_tmpkir0kenl_Test_allocated1_dafny0_fun-with-slices_no_hints.dfy
// keepToss: KEEP

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{}

////////TESTS////////

method TestSeqIntoArray1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
  var s := [10, 20];
  seqIntoArray(s, a, 1);
  assert a[..] == [1, 10, 20, 4, 5];
}

method TestSeqIntoArray2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 7, 8, 9, 10;
  var s := [100];
  seqIntoArray(s, a, 0);
  assert a[..] == [100, 8, 9, 10];
}

// Kept File 10:
// filename: 103_MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p5_no_hints.dfy
// filepath: ./run_1/new_tests/103_MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p5_no_hints.dfy
// keepToss: KEEP

type T = int

method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{}

////////TESTS////////

method TestPartition1() {
  var a := new T[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 1, 4, 1, 5;
  var pivotPos := partition(a);
  assert pivotPos == 2;
  assert a[..] == [1, 1, 3, 4, 5];
}

method TestPartition2() {
  var a := new T[3];
  a[0], a[1], a[2] := 7, 2, 9;
  var pivotPos := partition(a);
  assert pivotPos == 1;
  assert a[..] == [2, 7, 9];
}

// Kept File 11:
// filename: 57_Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_RotateRight_no_hints.dfy
// filepath: ./run_1/new_tests/57_Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_RotateRight_no_hints.dfy
// keepToss: KEEP

method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{}

////////TESTS////////

method TestRotateRight1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  RotateRight(a);
  assert a[0] == 4;
  assert a[1] == 1;
  assert a[2] == 2;
  assert a[3] == 3;
}

method TestRotateRight2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 10, 15;
  RotateRight(a);
  assert a[0] == 15;
  assert a[1] == 5;
  assert a[2] == 10;
}

// Kept File 12:
// filename: 68_dafny-synthesis_task_id_733_no_hints.dfy
// filepath: ./run_1/new_tests/68_dafny-synthesis_task_id_733_no_hints.dfy
// keepToss: KEEP

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{}

////////TESTS////////

method TestFindFirstOccurrence1() {
  var arr := new int[5];
  arr[0] := 1;
  arr[1] := 3;
  arr[2] := 3;
  arr[3] := 5;
  arr[4] := 7;
  var index := FindFirstOccurrence(arr, 3);
  assert index == 1;
}

method TestFindFirstOccurrence2() {
  var arr := new int[4];
  arr[0] := 2;
  arr[1] := 4;
  arr[2] := 6;
  arr[3] := 8;
  var index := FindFirstOccurrence(arr, 5);
  assert index == -1;
}

// Kept File 13:
// filename: 108_dafny-workout_tmp_tmp0abkw6f8_starter_ex12_no_hints.dfy
// filepath: ./run_1/new_tests/108_dafny-workout_tmp_tmp0abkw6f8_starter_ex12_no_hints.dfy
// keepToss: KEEP

method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 7, 2, 9, 1;
  var max_idx := FindMax(a);
  assert max_idx == 3;
}

method TestFindMax2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 5, 2, 5;
  var max_idx := FindMax(a);
  assert max_idx == 0 || max_idx == 1 || max_idx == 3;
}

// Kept File 14:
// filename: 85_dafny-synthesis_task_id_578_no_hints.dfy
// filepath: ./run_1/new_tests/85_dafny-synthesis_task_id_578_no_hints.dfy
// keepToss: KEEP

method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>) returns (r: seq<int>)
    requires |s1| == |s2| && |s2| == |s3|
    ensures |r| == 3 * |s1|
    ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i]
{}

////////TESTS////////

method TestInterleave1() {
  var s1 := [1, 3, 5];
  var s2 := [2, 4, 6];
  var s3 := [7, 8, 9];
  var r := Interleave(s1, s2, s3);
  assert r == [1, 2, 7, 3, 4, 8, 5, 6, 9];
}

method TestInterleave2() {
  var s1 := [10, 20];
  var s2 := [30, 40];
  var s3 := [50, 60];
  var r := Interleave(s1, s2, s3);
  assert r == [10, 30, 50, 20, 40, 60];
}

// Kept File 15:
// filename: 131_Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question5_no_hints.dfy
// filepath: ./run_1/new_tests/131_Workshop_tmp_tmp0cu11bdq_Workshop_Answers_Question5_no_hints.dfy
// keepToss: KEEP

method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{}

////////TESTS////////

method TestRev1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var old_a := [1, 2, 3, 4];
  rev(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestRev2() {
  var a := new int[3];
  a[0] := 5; a[1] := 10; a[2] := 15;
  var old_a := [5, 10, 15];
  rev(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}

