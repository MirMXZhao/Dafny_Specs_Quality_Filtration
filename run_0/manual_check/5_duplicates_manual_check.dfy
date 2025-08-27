// Kept File 1:
// filename: 7_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// filepath: ./run_0/new_filtered/7_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// keepToss: KEEP
// duplicateGroup: nan

method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}
// Kept File 2:
// filename: 0_dafny-synthesis_task_id_477.dfy
// filepath: ./run_0/new_filtered/0_dafny-synthesis_task_id_477.dfy
// keepToss: KEEP
// duplicateGroup: nan

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
// Kept File 3:
// filename: 4_QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// filepath: ./run_0/new_filtered/4_QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// keepToss: KEEP
// duplicateGroup: nan

function sorted(s : seq<int>) : bool {}

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{}

method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a 
{}

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
// filename: 3_dafny-synthesis_task_id_113.dfy
// filepath: ./run_0/new_filtered/3_dafny-synthesis_task_id_113.dfy
// keepToss: KEEP
// duplicateGroup: nan

predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}
// Kept File 5:
// filename: 5_dafny-exercise_tmp_tmpouftptir_absIt.dfy
// filepath: ./run_0/new_filtered/5_dafny-exercise_tmp_tmpouftptir_absIt.dfy
// keepToss: KEEP
// duplicateGroup: nan

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}
// Kept File 6:
// filename: 1_dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// filepath: ./run_0/new_filtered/1_dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// keepToss: KEEP
// duplicateGroup: nan

function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
// Kept File 7:
// filename: 2_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./run_0/new_filtered/2_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// keepToss: KEEP
// duplicateGroup: nan

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
// filename: 6_Clover_reverse.dfy
// filepath: ./run_0/new_filtered/6_Clover_reverse.dfy
// keepToss: KEEP
// duplicateGroup: nan

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}
