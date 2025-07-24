method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{}


method TestIsPalindrome1() {
  var x := ['r', 'a', 'c', 'e', 'c', 'a', 'r'];
  var result := IsPalindrome(x);
  assert result == true;
}

method TestIsPalindrome2() {
  var x := ['h', 'e', 'l', 'l', 'o'];
  var result := IsPalindrome(x);
  assert result == false;
}
