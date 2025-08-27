module InductiveThings {
  ghost predicate P(x: int)
  ghost predicate Q(x: int)

  least predicate A(x: int)
  {
    P(x) || B(x+1)
  }

  least predicate B(x: int)
  {
    Q(x) || A(x+1)
  }

  least lemma AA(x: int)
    requires A(x)
  {}

  least lemma BB(x: int)
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

  greatest lemma AA(x: int)
    ensures A(x)
  {}

  greatest lemma BB(x: int)
    ensures B(x)
  {}
}

module SingleThings {
  ghost predicate P(x: int)

  least predicate A(x: int)
  {
    P(x) || A(x+1)
  }

  least lemma AA(x: int)
    requires A(x)
  {}
}

////////TESTS////////

method TestAA1() {
  var x := 5;
  InductiveThings.AA(x);
}

method TestAA2() {
  var x := -3;
  InductiveThings.AA(x);
}
