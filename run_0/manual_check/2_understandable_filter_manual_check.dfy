// Kept File 1:
// filename: test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// keepToss: KEEP
// reasoning: The method names clearly indicate their purpose as assertion utilities for testing (assertEquals, assertTrue, assertFalse, etc.) which is easily interpretable.

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
// filename: dafny-exercise_tmp_tmpouftptir_absIt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-exercise_tmp_tmpouftptir_absIt.dfy
// keepToss: KEEP
// reasoning: The name "AbsIt" clearly suggests it computes absolute values, and the specification confirms it makes all array elements non-negative while preserving the array length.

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}

method Tester()
{}


// Kept File 3:
// filename: dafny-synthesis_task_id_477.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_477.dfy
// keepToss: KEEP
// reasoning: The method name "ToLowercase" clearly indicates it converts a string to lowercase, and the specifications support this purpose.

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
// Kept File 4:
// filename: dafny-synthesis_task_id_113.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-synthesis_task_id_113.dfy
// keepToss: KEEP
// reasoning: The method name "IsInteger" and the ensures clause make it clear this checks if a string represents an integer by verifying all characters are digits.

predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}
// Kept File 5:
// filename: dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// keepToss: KEEP
// reasoning: The function name "Expt" clearly indicates exponentiation (b raised to the power n), and the distributive lemma shows the mathematical property being proven about exponentiation.

function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

// Kept File 6:
// filename: Clover_reverse.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Clover_reverse.dfy
// keepToss: KEEP
// reasoning: The method name "reverse" clearly indicates it reverses the array, and the specification confirms this by ensuring each element at position i equals the old element at the mirrored position.

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

// Kept File 7:
// filename: Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// keepToss: KEEP
// reasoning: The method name "incrementArray" clearly indicates it should increment all elements in the array, which matches the specification.

method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}

// Kept File 8:
// filename: QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// keepToss: KEEP
// reasoning: The methods have clear, interpretable purposes based on their names: copyArr copies an array segment, mergeArr merges sorted segments, sort sorts an array, and sortAux is an auxiliary sorting method.

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

// Tossed File 1:
// filename: dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// filepath: ./DafnyBench/DafnyBench/dataset/new_body_removed/dafny-language-server_tmp_tmpkir0kenl_Test_hofs_Compilation.dfy
// keepToss: TOSS
// reasoning: This appears to be just test scaffolding with empty class and method definitions that provide no interpretable purpose or functionality.
// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {}

method Main() {}





