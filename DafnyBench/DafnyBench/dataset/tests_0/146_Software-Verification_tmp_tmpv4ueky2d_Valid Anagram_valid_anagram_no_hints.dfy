method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{}

////////TESTS////////

method testis_anagram1() {
  var result := is_anagram("listen", "silent");
  assert result == true;
}

method testis_anagram2() {
  var result := is_anagram("hello", "world");
  assert result == false;
}

method testis_anagram3() {
  var result := is_anagram("aab", "aba");
  assert result == true;
}

method testis_equal1() {
  var s := multiset{'a', 'b', 'c'};
  var t := multiset{'c', 'a', 'b'};
  var result := is_equal(s, t);
  assert result == true;
}

method testis_equal2() {
  var s := multiset{'a', 'b'};
  var t := multiset{'a', 'c'};
  var result := is_equal(s, t);
  assert result == false;
}

method testis_equal3() {
  var s := multiset{};
  var t := multiset{};
  var result := is_equal(s, t);
  assert result == true;
}
