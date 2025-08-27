const vowels: set<char> := {}

function FilterVowels(xs: seq<char>): seq<char>
{}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{}

////////TESTS////////

method TestFilterVowels1() {
  var xs := ['a', 'b', 'c', 'd', 'e'];
  var result := FilterVowels(xs);
  assert result == ['b', 'c', 'd'];
}

method TestFilterVowels2() {
  var xs := ['x', 'y', 'z'];
  var result := FilterVowels(xs);
  assert result == ['x', 'y', 'z'];
}

method TestFilterVowelsArray1() {
  var xs := new char[5];
  xs[0] := 'a'; xs[1] := 'b'; xs[2] := 'c'; xs[3] := 'd'; xs[4] := 'e';
  var ys := FilterVowelsArray(xs);
  assert ys[..] == ['b', 'c', 'd'];
}

method TestFilterVowelsArray2() {
  var xs := new char[3];
  xs[0] := 'x'; xs[1] := 'y'; xs[2] := 'z';
  var ys := FilterVowelsArray(xs);
  assert ys[..] == ['x', 'y', 'z'];
}
