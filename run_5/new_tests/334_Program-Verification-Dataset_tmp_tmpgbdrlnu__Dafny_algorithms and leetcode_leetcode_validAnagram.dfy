method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{}

////////TESTS////////

method TesttoMultiset1() {
  var s := "hello";
  var mset := toMultiset(s);
  assert mset == multiset{'h', 'e', 'l', 'l', 'o'};
}

method TesttoMultiset2() {
  var s := "abc";
  var mset := toMultiset(s);
  assert mset == multiset{'a', 'b', 'c'};
}

method TestmsetEqual1() {
  var s := multiset{'a', 'b', 'c'};
  var t := multiset{'a', 'b', 'c'};
  var equal := msetEqual(s, t);
  assert equal == true;
}

method TestmsetEqual2() {
  var s := multiset{'a', 'b', 'c'};
  var t := multiset{'a', 'b', 'd'};
  var equal := msetEqual(s, t);
  assert equal == false;
}

method TestisAnagram1() {
  var s := "listen";
  var t := "silent";
  var equal := isAnagram(s, t);
  assert equal == true;
}

method TestisAnagram2() {
  var s := "hello";
  var t := "world";
  var equal := isAnagram(s, t);
  assert equal == false;
}
