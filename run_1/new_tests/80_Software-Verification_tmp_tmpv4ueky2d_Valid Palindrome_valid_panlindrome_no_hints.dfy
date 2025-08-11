method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{}

////////TESTS////////

method TestisPalindrome1() {
  var s := new char[5] ['r', 'a', 'c', 'e', 'r'];
  var result := isPalindrome(s);
  assert result == true;
}

method TestisPalindrome2() {
  var s := new char[4] ['h', 'e', 'l', 'l'];
  var result := isPalindrome(s);
  assert result == false;
}
