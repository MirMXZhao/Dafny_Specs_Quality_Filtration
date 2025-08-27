method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}

////////TESTS////////

method TestLongestCommonPrefix1() {
  var str1 := ['a', 'b', 'c', 'd'];
  var str2 := ['a', 'b', 'x', 'y'];
  var prefix := LongestCommonPrefix(str1, str2);
  assert prefix == ['a', 'b'];
}

method TestLongestCommonPrefix2() {
  var str1 := ['h', 'e', 'l', 'l', 'o'];
  var str2 := ['h', 'e', 'l', 'p'];
  var prefix := LongestCommonPrefix(str1, str2);
  assert prefix == ['h', 'e', 'l'];
}
