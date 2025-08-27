predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{}

////////TESTS////////

method TestCountUppercase1() {
  var count := CountUppercase("Hello World");
  assert count == 2;
}

method TestCountUppercase2() {
  var count := CountUppercase("HELLO");
  assert count == 5;
}
