predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{}

////////TESTS////////

method TestIsInteger1() {
  var result := IsInteger("12345");
  assert result == true;
}

method TestIsInteger2() {
  var result := IsInteger("123a45");
  assert result == false;
}
