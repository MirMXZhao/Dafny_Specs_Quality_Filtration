// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate ContainsNothingBut5(s: set<int>)
{}

predicate YeahContains5(s: set<int>)
{}

predicate ViaSetComprehension(s: set<int>) {}

predicate LambdaTest(s: set<int>) {}

predicate ViaMapComprehension(s: set<int>) {}

predicate Contains5(s: set<int>)
{}

datatype R = MakeR(int) | Other

predicate RIs5(r: R) {}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
}
lemma NonemptyMap(x: int, s: map<int,bool>)
  requires x in s.Keys
  ensures |s| != 0
{
}

method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
{}

