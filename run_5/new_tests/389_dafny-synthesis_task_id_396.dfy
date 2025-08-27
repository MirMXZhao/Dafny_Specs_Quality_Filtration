method StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{}

////////TESTS////////

method TestStartAndEndWithSameChar1() {
  var result := StartAndEndWithSameChar("hello");
  assert result == false;
}

method TestStartAndEndWithSameChar2() {
  var result := StartAndEndWithSameChar("radar");
  assert result == true;
}
