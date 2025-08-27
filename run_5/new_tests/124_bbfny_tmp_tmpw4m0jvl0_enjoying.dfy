method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{}

method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c
  ensures a == c || b == c
{}

function max(a: int, b: int): int
{}

function abs(x: int): int
{}
method Abs(x: int) returns (y: int)
  ensures y == abs(x)
{
  return abs(x);
}

method m(n: nat)
{}

function fib(n: nat): nat
{}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{}

method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{}
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

predicate sorted'(a: array?<int>)
  reads a
{
  forall j, k :: a != null && 0 <= j < k < a.Length ==> a[j] <= a[k]
}

////////TESTS////////

method TestMultipleReturns1() {
  var more, less := MultipleReturns(5, 2);
  assert more > 5;
  assert less < 5;
}

method TestMultipleReturns2() {
  var more, less := MultipleReturns(10, 3);
  assert more > 10;
  assert less < 10;
}

method TestMax1() {
  var c := Max(5, 3);
  assert c == 5;
}

method TestMax2() {
  var c := Max(2, 7);
  assert c == 7;
}

method TestAbs1() {
  var y := Abs(-5);
  assert y == 5;
}

method TestAbs2() {
  var y := Abs(3);
  assert y == 3;
}

method TestFind1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 3, 5, 7;
  var index := Find(a, 5);
  assert index == 2;
}

method TestFind2() {
  var a := new int[3];
  a[0], a[1], a[2] := 2, 4, 6;
  var index := Find(a, 9);
  assert index < 0;
}

method TestFindMax1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 5, 3;
  var i := FindMax(a);
  assert i == 1;
}

method TestFindMax2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 8, 2, 9, 1;
  var i := FindMax(a);
  assert i == 2;
}
