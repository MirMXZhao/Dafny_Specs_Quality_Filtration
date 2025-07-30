method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{}

////////TESTS////////

method TestIsPalindrome1() {
  var x := ['a', 'b', 'a'];
  var result := IsPalindrome(x);
  assert result == true;
}

method TestIsPalindrome2() {
  var x := ['a', 'b', 'c'];
  var result := IsPalindrome(x);
  assert result == false;
}

method TestIsPalindrome3() {
  var x := [];
  var result := IsPalindrome(x);
  assert result == true;
}

method TestIsPalindrome4() {
  var x := ['x'];
  var result := IsPalindrome(x);
  assert result == true;
}
