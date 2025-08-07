method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{}

////////TESTS////////

method TestAllCharactersSame1() {
  var result := AllCharactersSame("aaaa");
  assert result == true;
}

method TestAllCharactersSame2() {
  var result := AllCharactersSame("abcd");
  assert result == false;
}

method TestAllCharactersSame3() {
  var result := AllCharactersSame("");
  assert result == true;
}

method TestAllCharactersSame4() {
  var result := AllCharactersSame("a");
  assert result == true;
}
