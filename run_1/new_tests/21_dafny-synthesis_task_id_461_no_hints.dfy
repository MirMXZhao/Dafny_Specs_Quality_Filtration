predicate IsUpperCase(c: char)
{}

method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{}

////////TESTS////////

method TestCountUppercase1() {
  var s := "Hello World";
  var count := CountUppercase(s);
  assert count == 2;
}

method TestCountUppercase2() {
  var s := "abc def";
  var count := CountUppercase(s);
  assert count == 0;
}
