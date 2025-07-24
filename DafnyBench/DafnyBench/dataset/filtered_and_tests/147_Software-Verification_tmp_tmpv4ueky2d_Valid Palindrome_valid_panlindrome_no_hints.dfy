method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{}



method TestIsPalindrome1() {
  var s := new char[5];
  s[0] := 'r'; s[1] := 'a'; s[2] := 'c'; s[3] := 'e'; s[4] := 'r';
  var result := isPalindrome(s);
  assert result == true;
}

method TestIsPalindrome2() {
  var s := new char[5];
  s[0] := 'h'; s[1] := 'e'; s[2] := 'l'; s[3] := 'l'; s[4] := 'o';
  var result := isPalindrome(s);
  assert result == false;
}
