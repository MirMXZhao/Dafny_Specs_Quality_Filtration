predicate isPrefixPredicate(pre: string, str:string)
{
  |str| >= |pre| && pre <= str
}

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{}

predicate isSubstringPredicate (sub: string, str:string)
{
  |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{}

predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
   forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{}

////////TESTS////////

method TestisPrefix1() {
  var pre := "hello";
  var str := "hello world";
  var res := isPrefix(pre, str);
  assert res == true;
}

method TestisPrefix2() {
  var pre := "world";
  var str := "hello";
  var res := isPrefix(pre, str);
  assert res == false;
}

method TestisSubstring1() {
  var sub := "ell";
  var str := "hello world";
  var res := isSubstring(sub, str);
  assert res == true;
}

method TestisSubstring2() {
  var sub := "xyz";
  var str := "hello world";
  var res := isSubstring(sub, str);
  assert res == false;
}

method TesthaveCommonKSubstring1() {
  var k := 2;
  var str1 := "hello";
  var str2 := "world";
  var found := haveCommonKSubstring(k, str1, str2);
  assert found == true;
}

method TesthaveCommonKSubstring2() {
  var k := 3;
  var str1 := "abc";
  var str2 := "def";
  var found := haveCommonKSubstring(k, str1, str2);
  assert found == false;
}

method TestmaxCommonSubstringLength1() {
  var str1 := "hello";
  var str2 := "world";
  var len := maxCommonSubstringLength(str1, str2);
  assert len == 2;
}

method TestmaxCommonSubstringLength2() {
  var str1 := "abc";
  var str2 := "def";
  var len := maxCommonSubstringLength(str1, str2);
  assert len == 0;
}
