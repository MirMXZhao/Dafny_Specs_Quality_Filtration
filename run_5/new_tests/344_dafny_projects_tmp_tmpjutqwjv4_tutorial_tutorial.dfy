function fib(n: nat): nat
{}

method ComputeFib(n: nat) returns (ret: nat)
  ensures ret == fib(n)
{}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> (forall k :: 0 <= k < a.Length ==> a[k] != key)
{}

predicate sorted(a: array<int>)
  reads a
{
  forall n, m :: 0 <= n < m < a.Length ==> a[n] <= a[m]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{}

function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
{}

lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{}

method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{}

function count(a: seq<bool>): nat
{}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{}

class Node
{}

predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}

predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{}

predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{}

lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
{}

lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{}

////////TESTS////////

method TestComputeFib1() {
  var ret := ComputeFib(5);
  assert ret == fib(5);
}

method TestComputeFib2() {
  var ret := ComputeFib(0);
  assert ret == fib(0);
}

method TestFind1() {
  var a := new int[4] := [1, 3, 5, 7];
  var index := Find(a, 5);
  assert index == 2;
}

method TestFind2() {
  var a := new int[3] := [2, 4, 6];
  var index := Find(a, 9);
  assert index < 0;
}

method TestBinarySearch1() {
  var a := new int[4] := [1, 3, 5, 7];
  var index := BinarySearch(a, 3);
  assert index == 1;
}

method TestBinarySearch2() {
  var a := new int[3] := [2, 4, 6];
  var index := BinarySearch(a, 5);
  assert index < 0;
}

method TestFindZero1() {
  var a := new int[4] := [1, 2, 0, 3];
  var index := FindZero(a);
  assert index == 2;
}

method TestFindZero2() {
  var a := new int[3] := [1, 2, 3];
  var index := FindZero(a);
  assert index < 0;
}
