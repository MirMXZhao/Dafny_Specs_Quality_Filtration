method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{}

////////TESTS////////

method TestIsPalindrome1() {
  var s := new char[5];
  s[0] := 'r'; s[1] := 'a'; s[2] := 'c'; s[3] := 'e'; s[4] := 'r';
  var result := isPalindrome(s);
  assert result == true;
}

method TestIsPalindrome2() {
  var s := new char[3];
  s[0] := 'a'; s[1] := 'b'; s[2] := 'a';
  var result := isPalindrome(s);
  assert result == true;
}

method TestIsPalindrome3() {
  var s := new char[5];
  s[0] := 'a'; s[1] := 'b'; s[2] := 'c'; s[3] := 'd'; s[4] := 'e';
  var result := isPalindrome(s);
  assert result == false;
}

method TestIsPalindrome4() {
  var s := new char[1];
  s[0] := 'x';
  var result := isPalindrome(s);
  assert result == true;
}
