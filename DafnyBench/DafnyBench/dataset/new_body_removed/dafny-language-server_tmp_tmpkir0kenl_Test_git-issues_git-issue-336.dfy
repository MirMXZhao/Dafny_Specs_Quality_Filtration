// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma TestMap(a: map<int, (int,int)>) {}

lemma TestSet0(a: set<int>) {}

lemma TestSet1(a: set<int>, m: int) {}

lemma TestSet2(a: set<int>, m: int)
  requires m in a && m < 7
{}

