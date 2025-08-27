// Kept File 1:
// filename: 1_dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// filepath: ./run_0/new_tests/1_dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy
// keepToss: KEEP

function Expt(b: int, n: nat): int
  requires n >= 0
{}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{}

lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

////////TESTS////////

method TestExpt1() {
  var res := expt(2, 3);
  assert res == 8;
}

method TestExpt2() {
  var res := expt(5, 0);
  assert res == 1;
}

// Kept File 2:
// filename: 3_dafny-synthesis_task_id_113.dfy
// filepath: ./run_0/new_tests/3_dafny-synthesis_task_id_113.dfy
// keepToss: KEEP

predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}

////////TESTS////////

method TestIsInteger1() {
  var result := IsInteger("123");
  assert result == true;
}

method TestIsInteger2() {
  var result := IsInteger("12a3");
  assert result == false;
}

// Kept File 3:
// filename: 0_dafny-synthesis_task_id_477.dfy
// filepath: ./run_0/new_tests/0_dafny-synthesis_task_id_477.dfy
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

////////TESTS////////

method TestToLowercase1() {
  var s := "Hello World";
  var v := ToLowercase(s);
  assert v == "hello world";
}

method TestToLowercase2() {
  var s := "ABC123def";
  var v := ToLowercase(s);
  assert v == "abc123def";
}

// Kept File 4:
// filename: 5_dafny-exercise_tmp_tmpouftptir_absIt.dfy
// filepath: ./run_0/new_tests/5_dafny-exercise_tmp_tmpouftptir_absIt.dfy
// keepToss: KEEP

method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}

////////TESTS////////

method TestAbsIt1() {
  var s := new int[4];
  s[0] := -3;
  s[1] := 5;
  s[2] := -7;
  s[3] := 0;
  AbsIt(s);
  assert s[0] == 3;
  assert s[1] == 5;
  assert s[2] == 7;
  assert s[3] == 0;
}

method TestAbsIt2() {
  var s := new int[3];
  s[0] := 10;
  s[1] := -2;
  s[2] := 8;
  AbsIt(s);
  assert s[0] == 10;
  assert s[1] == 2;
  assert s[2] == 8;
}

// Kept File 5:
// filename: 6_Clover_reverse.dfy
// filepath: ./run_0/new_tests/6_Clover_reverse.dfy
// keepToss: KEEP

method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{}

////////TESTS////////

method TestReverse1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  reverse(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestReverse2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 10, 15;
  reverse(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}

// Kept File 6:
// filename: 4_QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// filepath: ./run_0/new_tests/4_QS_BoilerPlate1_tmp_tmpa29vtz9__Ex2.dfy
// keepToss: KEEP

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

////////TESTS////////

method TestCopyArr1() {
  var a := new int[5] [1, 2, 3, 4, 5];
  var ret := copyArr(a, 1, 4);
  assert ret[..] == [2, 3, 4];
}

method TestCopyArr2() {
  var a := new int[3] [10, 20, 30];
  var ret := copyArr(a, 0, 2);
  assert ret[..] == [10, 20];
}

// Kept File 7:
// filename: 7_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// filepath: ./run_0/new_tests/7_Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array.dfy
// keepToss: KEEP

method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{}

////////TESTS////////

method TestIncrementArray1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  incrementArray(a);
  assert a[0] == 2 && a[1] == 3 && a[2] == 4;
}

method TestIncrementArray2() {
  var a := new int[1];
  a[0] := -5;
  incrementArray(a);
  assert a[0] == -4;
}

// Kept File 8:
// filename: 2_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
// filepath: ./run_0/new_tests/2_test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_Utils.dfy
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

////////TESTS////////

method TestBelowZero1() {
  var operations := [1, 2, -4, 5];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == -1;
  assert s[4] == 4;
  assert result == true;
}

method TestBelowZero2() {
  var operations := [1, 2, 3, 1];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == 6;
  assert s[4] == 7;
  assert result == false;
}

