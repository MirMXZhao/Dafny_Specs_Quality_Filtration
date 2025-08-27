method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}

////////TESTS////////

method TestIsAnagram1() {
  var s := "listen";
  var t := "silent";
  var result := is_anagram(s, t);
  assert result == true;
}

method TestIsAnagram2() {
  var s := "hello";
  var t := "world";
  var result := is_anagram(s, t);
  assert result == false;
}

method TestIsEqual1() {
  var s := multiset{'a', 'b', 'c'};
  var t := multiset{'c', 'b', 'a'};
  var result := is_equal(s, t);
  assert result == true;
}

method TestIsEqual2() {
  var s := multiset{'a', 'b'};
  var t := multiset{'a', 'c'};
  var result := is_equal(s, t);
  assert result == false;
}
