// shenanigans going through the dafny tutorial

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{}

method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c
  ensures a == c || b == c
{}

method Testing() {}

function max(a: int, b: int): int
{}
method Testing'() {
}

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
{}

predicate sorted'(a: array?<int>) // Change the type
  reads a
{}
