// Kept File 1:
// filename: test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// keepToss: KEEP
// reasoning: This defines assertion utility methods with preconditions and postconditions, which is not a direct formula.

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

// Kept File 2:
// filename: dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// keepToss: KEEP
// reasoning: This involves recursive exponentiation logic and mathematical proofs, not a direct formula.

function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

// Kept File 3:
// filename: QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// keepToss: KEEP
// reasoning: This specification involves multiple methods for array copying, merging, and sorting with complex preconditions and postconditions, which is not a direct formula.

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

// Kept File 4:
// filename: dafny-exercise_tmp_tmpouftptir_absIt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-exercise_tmp_tmpouftptir_absIt.dfy
// keepToss: KEEP
// reasoning: This specification involves array modification logic with conditional transformations based on element values, which is not a direct formula.

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}

method Tester()
{}


// Kept File 5:
// filename: dafny-synthesis_task_id_113.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_113.dfy
// keepToss: KEEP
// reasoning: This involves character validation logic and universal quantification over string indices, which is not a direct formula.

predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}
// Kept File 6:
// filename: dafny-synthesis_task_id_477.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_477.dfy
// keepToss: KEEP
// reasoning: The specification involves conditional logic and character-by-character transformation rules, which is not a direct formula.

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
// Kept File 7:
// filename: Clover_reverse.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_reverse.dfy
// keepToss: KEEP
// reasoning: This involves array manipulation and indexing logic to reverse elements, which is not a direct formula.

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

// Kept File 8:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// keepToss: KEEP
// reasoning: This specification defines a generic class and main method, which is not a direct formula.

// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {}

method Main() {}



// Kept File 9:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// keepToss: KEEP
// reasoning: This involves modifying array elements with iteration logic, not a direct formula.

method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}

// Tossed File 1:
// filename: Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy
// keepToss: TOSS
// reasoning: This specification is just a direct formula for computing integer square roots with different algorithmic complexities.
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




