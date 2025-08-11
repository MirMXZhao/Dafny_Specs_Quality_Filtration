method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{}

////////TESTS////////

method TestAllCharactersSame1() {
  var s := "aaaa";
  var result := AllCharactersSame(s);
  assert result == true;
}

method TestAllCharactersSame2() {
  var s := "abc";
  var result := AllCharactersSame(s);
  assert result == false;
}
