predicate IsUpperCase(c: char)
{}

method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{}

////////TESTS////////

method TestCountUppercase1() {
  var count := CountUppercase("HeLLo");
  assert count == 3;
}

method TestCountUppercase2() {
  var count := CountUppercase("world");
  assert count == 0;
}

method TestCountUppercase3() {
  var count := CountUppercase("");
  assert count == 0;
}

method TestIsUpperCase1() {
  var result := IsUpperCase('A');
  assert result == true;
}

method TestIsUpperCase2() {
  var result := IsUpperCase('a');
  assert result == false;
}
