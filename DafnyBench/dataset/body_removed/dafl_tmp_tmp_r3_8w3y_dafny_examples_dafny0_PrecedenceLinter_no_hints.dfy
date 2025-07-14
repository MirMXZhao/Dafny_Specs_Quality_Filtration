// RUN: %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P0(A: bool, B: bool, C: bool) {}

predicate P1(A: bool, B: bool, C: bool) {}

predicate P2(A: bool, B: bool, C: bool) {}

predicate P3(A: bool, B: bool, C: bool, D: bool) {}

predicate P4(A: bool, B: bool, C: bool, D: bool) {}

predicate P5(A: bool, B: bool, C: bool) {}

predicate P6(A: bool, B: bool, C: bool) {}

predicate Q0(A: bool, B: bool, C: bool, D: bool) {}

predicate Q1(A: bool, B: bool, C: bool, D: bool) {}

predicate Q2(A: bool, B: bool, C: bool, D: bool) {}

predicate Q3(A: bool, B: bool, C: bool, D: bool) {}

predicate Q4(A: bool, B: bool, C: bool, D: bool) {}

predicate Q4a(A: bool, B: bool, C: bool, D: bool) {}

predicate Q4b(A: bool, B: bool, C: bool, D: bool) {}

predicate Q4c(A: bool, B: bool, C: bool, D: bool) {}

predicate Q4d(A: bool, B: bool, C: bool, D: bool) {}

predicate Q5(A: bool, B: bool, C: bool, D: bool) {}

predicate Q6(A: bool, B: bool, C: bool, D: bool) {}

predicate Q7(A: bool, B: bool, C: bool, D: bool) {}

predicate Q8(A: bool, B: bool, C: bool, D: bool) {}

predicate Q8a(A: bool, B: bool, C: bool, D: bool) {}

predicate Q8b(A: bool, B: bool, C: bool, D: bool) {}

predicate Q8c(t: int, x: int, y: int)
{}

predicate Q8d(t: int, x: int, y: int)
{}

predicate Q9(A: bool, B: bool, C: bool) {
  A ==> B ==>
  C
}

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool) {}

lemma Injective()
  ensures forall x, y ::
    Negate(x) == Negate(y)
    ==> x == y
{
}

function Negate(x: int): int {
  -x
}

predicate Quant0(s: string) {}

predicate Quant1(m: array2<string>, P: int -> bool)
  reads m
{}

predicate Quant2(s: string) {}

ghost predicate Quant3(f: int -> int, g: int -> int) {}

ghost predicate Quant4(f: int -> int, g: int -> int) {}

ghost predicate Quant5(f: int -> int, g: int -> int) {}

function If0(s: string): int {}

function If1(s: string): int {}

function If2(s: string): int {}

function If3(s: string): int {}

predicate Waterfall(A: bool, B: bool, C: bool, D: bool, E: bool) {}

ghost predicate MoreOps0(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate MoreOps1(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate MoreOps2(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate MoreOps3(P: int -> bool, Q: int -> bool, R: int -> bool) {}

ghost predicate MoreOps4(P: int -> bool, Q: int -> bool, R: int -> bool) {}

lemma IntLemma(x: int)

function StmtExpr0(x: int): int {}

function StmtExpr1(x: int): int {}

function StmtExpr2(x: int): int {}

function StmtExpr3(x: int): int {}

function FunctionWithDefaultParameterValue(x: int, y: int := 100): int

function UseDefaultValues(x: int): int {}

function Square(x: int): int {
  x * x
}

predicate Let0(lo: int, hi: int)
  requires lo <= hi
{}

ghost predicate Let1(P: int -> bool) {}

predicate SomeProperty<X>(x: X)

method Parentheses0(arr: array<int>, P: int -> bool)
{}

method Parentheses1(w: bool, x: int)
{}

datatype Record = Record(x: int, y: int)

method Parentheses2(w: bool, x: int, y: int)
{}

method Parentheses3(w: bool, arr: array<int>, m: array2<int>, i: nat, j: nat)
  requires i < j < arr.Length <= m.Length0 <= m.Length1
{}

codatatype Stream = More(head: int, tail: Stream)

method Parentheses4(w: bool, s: Stream, t: Stream)
{}
/**** revisit the following when the original match'es are being resolved (https://github.com/dafny-lang/dafny/pull/2734)
datatype Color = Red | Blue

method Parentheses5(w: bool, color: Color) {}
***/

module MyModule {
  function MyFunction(x: int): int
  lemma Lemma(x: int)
}

module QualifiedNames {
  import MyModule

  predicate P(x: int) {}

  predicate Q(x: int) {}

  function F(): int
  {}

  predicate R(x: int) {}
}  

module MatchAcrossMultipleLines {
  datatype PQ = P(int) | Q(bool)

  method M(s: set<PQ>)
    requires
      (forall pq | pq in s :: match pq {})
  {
  }

  datatype YZ = Y | Z

  function F(A: bool, B: int, C: YZ): int
    requires C != Y
  {}
}

