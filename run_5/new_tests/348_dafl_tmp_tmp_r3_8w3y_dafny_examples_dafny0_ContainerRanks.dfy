datatype Abc = End | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
}

////////TESTS////////

method TestSeqRank01() {
  var a := End;
  SeqRank0(a);
  assert a != Wrapper([a]);
}

method TestSeqRank02() {
  var a := Wrapper([End]);
  SeqRank0(a);
  assert a != Wrapper([a]);
}

method TestSeqRank11() {
  var s := [End];
  SeqRank1(s);
  assert s[0] != Wrapper(s);
}

method TestSeqRank12() {
  var s := [Wrapper([End]), End];
  SeqRank1(s);
  assert s[0] != Wrapper(s);
}

method TestMultisetRank1() {
  var a := Def.End;
  MultisetRank(a);
  assert a != MultiWrapper(multiset{a});
}

method TestMultisetRank2() {
  var a := MultiWrapper(multiset{Def.End});
  MultisetRank(a);
  assert a != MultiWrapper(multiset{a});
}

method TestSetRank1() {
  var a := Ghi.End;
  SetRank(a);
  assert a != SetWrapper({a});
}

method TestSetRank2() {
  var a := SetWrapper({Ghi.End});
  SetRank(a);
  assert a != SetWrapper({a});
}
