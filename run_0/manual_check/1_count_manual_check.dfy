// Kept File 1:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 1
// num_lines: 6
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}

// Kept File 2:
// filename: Clover_reverse.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_reverse.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 1
// num_requires: 0
// num_lines: 5
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

// Kept File 3:
// filename: dafny-exercise_tmp_tmpouftptir_absIt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-exercise_tmp_tmpouftptir_absIt.dfy
// num_methods: 2
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 2
// num_requires: 0
// num_lines: 10
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}

method Tester()
{}


// Kept File 4:
// filename: dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// num_methods: 1
// num_lemmas: 1
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 2
// num_requires: 1
// num_lines: 12
// num_no_ensures: 1
// num_no_requires: 2
// num_none_either: 0
// keepToss: KEEP

function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

// Kept File 5:
// filename: Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// num_methods: 3
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 3
// num_lines: 17
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 0
// keepToss: KEEP

method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


// Kept File 6:
// filename: QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// num_methods: 4
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 0
// num_ensures: 8
// num_requires: 4
// num_lines: 38
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

function sorted(s : seq<int>) : bool {}


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{}


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a 
{}

// Ex3

method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
{}

method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  decreases r - l
{}

// Kept File 7:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 1
// num_functions: 0
// num_predicates: 0
// num_ensures: 0
// num_requires: 0
// num_lines: 9
// num_no_ensures: 0
// num_no_requires: 0
// num_none_either: 1
// keepToss: KEEP

// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {}

method Main() {}



// Kept File 8:
// filename: dafny-synthesis_task_id_477.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_477.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 1
// num_predicates: 2
// num_ensures: 2
// num_requires: 0
// num_lines: 17
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 1
// keepToss: KEEP

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{}

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{}
// Kept File 9:
// filename: test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// num_methods: 6
// num_lemmas: 0
// num_classes: 1
// num_functions: 0
// num_predicates: 0
// num_ensures: 3
// num_requires: 3
// num_lines: 22
// num_no_ensures: 3
// num_no_requires: 3
// num_none_either: 0
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

// Kept File 10:
// filename: dafny-synthesis_task_id_113.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_113.dfy
// num_methods: 1
// num_lemmas: 0
// num_classes: 0
// num_functions: 0
// num_predicates: 1
// num_ensures: 1
// num_requires: 0
// num_lines: 8
// num_no_ensures: 0
// num_no_requires: 1
// num_none_either: 0
// keepToss: KEEP

predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}
