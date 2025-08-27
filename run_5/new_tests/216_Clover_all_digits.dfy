method allDigits(s: string) returns (result: bool)
  ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{}

////////TESTS////////

method TestAllDigits1() {
  var s := "12345";
  var result := allDigits(s);
  assert result == true;
}

method TestAllDigits2() {
  var s := "123a45";
  var result := allDigits(s);
  assert result == false;
}
