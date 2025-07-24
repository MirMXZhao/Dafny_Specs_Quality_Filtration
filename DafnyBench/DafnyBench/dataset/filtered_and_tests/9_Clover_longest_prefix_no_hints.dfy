method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{}


method TestLongestCommonPrefix1() {
  var str1 := ['h', 'e', 'l', 'l', 'o'];
  var str2 := ['h', 'e', 'l', 'p'];
  var prefix := LongestCommonPrefix(str1, str2);
  assert prefix == ['h', 'e', 'l'];
}

method TestLongestCommonPrefix2() {
  var str1 := ['c', 'a', 't'];
  var str2 := ['d', 'o', 'g'];
  var prefix := LongestCommonPrefix(str1, str2);
  assert prefix == [];
}
