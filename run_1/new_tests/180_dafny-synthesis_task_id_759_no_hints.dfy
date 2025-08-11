method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{}

////////TESTS////////

method TestIsDecimalWithTwoPrecision1() {
  var s := "12.34";
  var result := IsDecimalWithTwoPrecision(s);
  assert result == true;
}

method TestIsDecimalWithTwoPrecision2() {
  var s := "12.345";
  var result := IsDecimalWithTwoPrecision(s);
  assert result == false;
}
