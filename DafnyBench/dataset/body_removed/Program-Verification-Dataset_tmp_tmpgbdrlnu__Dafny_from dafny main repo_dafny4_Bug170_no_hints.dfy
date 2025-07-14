// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module InductiveThings {
  ghost predicate P(x: int)
  ghost predicate Q(x: int)

  least predicate A(x: int)
  {}

  least predicate B(x: int)
  {}

  least lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    requires A(x)
  {}

  least lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    requires B(x)
  {}
}

module CoThings {
  greatest predicate A(x: int)
  {
    B(x+1)
  }

  greatest predicate B(x: int)
  {
    A(x+1)
  }

  greatest lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    ensures A(x)
  {
    BB(x+1);
  }

  greatest lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    ensures B(x)
  {
    AA(x+1);
  }
}

module SingleThings {
  ghost predicate P(x: int)

  least predicate A(x: int)
  {}

  least lemma AA(x: int)  // should be specialized just for A
    requires A(x)
  {}
}

