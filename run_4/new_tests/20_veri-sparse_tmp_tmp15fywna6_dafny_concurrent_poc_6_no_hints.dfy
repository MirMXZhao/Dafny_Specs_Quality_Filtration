class Process {}

function sum(s : seq<nat>) : nat
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{}

lemma sum0(s : seq<nat>)
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  {}

lemma sum_const(s : seq<nat>, x : nat)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
  {
  }

lemma sum_eq(s1 : seq<nat>, s2 : seq<nat>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  {

  }

lemma sum_exept(s1 : seq<nat>, s2 : seq<nat>, x : nat, j : nat)
requires |s1| == |s2|
requires j < |s1|
requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
requires s1[j] == s2[j] + x
ensures sum(s1) == sum(s2) + x
{}


function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
{}

class MatrixVectorMultiplier
{   

    ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers : array<nat>)
        reads this, y, P, M, leftOvers
    {}


    constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers : array<nat>)
        requires (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        requires |processes| == leftOvers.Length 
        requires |processes| == M_.Length0
        requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
        requires (forall p, q :: p in processes && q in processes ==> p != q)
        requires (forall p :: p in processes ==> 0 <= p.row < M_.Length0)

        requires (forall p :: p in processes ==> 0 == p.curColumn)
        requires (forall p :: p in processes ==> p.opsLeft == M_.Length1)

        requires (forall i :: 0 <= i < y_.Length ==> y_[i] == 0)
        requires y_.Length == M_.Length0

        requires |x_| == M_.Length1
        requires M_.Length0 > 0
        requires |x_| > 0
        ensures (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        ensures Valid(M_, x_, y_, processes, leftOvers)
    {
        
    }

    method processNext(M: array2<int>, x: seq<int>, y: array<int>, P : set<Process>, leftOvers : array<nat>)
        requires Valid(M, x, y, P, leftOvers)
        requires exists p :: (p in P && p.opsLeft > 0)
        requires sum(leftOvers[..]) > 0
        modifies this, y, P, leftOvers
        requires (forall p, q :: p in P && q in P && p != q ==> p.row != q.row)

        ensures Valid(M, x, y, P, leftOvers)
        ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    {}


}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires |processes| == M.Length0
    requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
    requires (forall p, q :: p in processes && q in processes ==> p != q)
    requires (forall p :: p in processes ==> 0 <= p.row < M.Length0)

    requires (forall p :: p in processes ==> 0 == p.curColumn)
    requires (forall p :: p in processes ==> p.opsLeft == M.Length1)

    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    modifies processes, M, x
{}

////////TESTS////////

method TestRun1() {
  var processes := {};
  var M := new int[0, 1];
  var x := new int[1];
  x[0] := 5;
  var y := Run(processes, M, x);
  assert y.Length == 0;
}

method TestRun2() {
  var p1 := new Process;
  p1.row := 0;
  p1.curColumn := 0;
  p1.opsLeft := 2;
  var processes := {p1};
  var M := new int[1, 2];
  M[0, 0] := 3;
  M[0, 1] := 4;
  var x := new int[2];
  x[0] := 1;
  x[1] := 2;
  var y := Run(processes, M, x);
  assert y.Length == 1;
}
