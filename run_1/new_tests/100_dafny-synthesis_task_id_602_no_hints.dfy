method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{}

////////TESTS////////

method TestFindFirstRepeatedChar1() {
  var s := "hello";
  var found, c := FindFirstRepeatedChar(s);
  assert found == true;
  assert c == 'l';
}

method TestFindFirstRepeatedChar2() {
  var s := "abcd";
  var found, c := FindFirstRepeatedChar(s);
  assert found == false;
  assert c == 'a';
}
