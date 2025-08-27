const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}

////////TESTS////////

method TestFilterVowels1() {
  var xs := ['h', 'e', 'l', 'l', 'o'];
  var result := FilterVowels(xs);
  assert result == ['h', 'l', 'l'];
}

method TestFilterVowels2() {
  var xs := ['a', 'b', 'c'];
  var result := FilterVowels(xs);
  assert result == ['b', 'c'];
}

method TestFilterVowelsArray1() {
  var xs := new char[5];
  xs[0] := 'h'; xs[1] := 'e'; xs[2] := 'l'; xs[3] := 'l'; xs[4] := 'o';
  var ys := FilterVowelsArray(xs);
  assert ys[..] == ['h', 'l', 'l'];
}

method TestFilterVowelsArray2() {
  var xs := new char[3];
  xs[0] := 'a'; xs[1] := 'b'; xs[2] := 'c';
  var ys := FilterVowelsArray(xs);
  assert ys[..] == ['b', 'c'];
}
