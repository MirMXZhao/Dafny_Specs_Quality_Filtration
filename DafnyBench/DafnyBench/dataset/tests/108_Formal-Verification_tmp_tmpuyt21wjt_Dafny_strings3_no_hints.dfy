predicate isPrefixPred(pre:string, str:string)
{}

predicate isNotPrefixPred(pre:string, str:string)
{}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{}

predicate isSubstringPred(sub:string, str:string)
{}

predicate isNotSubstringPred(sub:string, str:string)
{}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
{}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{}

////////TESTS////////

method testIsPrefix1() {
  var res := isPrefix("abc", "abcdef");
  assert res == true;
}

method testIsPrefix2() {
  var res := isPrefix("xyz", "abcdef");
  assert res == false;
}

method testIsPrefix3() {
  var res := isPrefix("", "hello");
  assert res == true;
}

method testIsSubstring1() {
  var res := isSubstring("bcd", "abcdef");
  assert res == true;
}

method testIsSubstring2() {
  var res := isSubstring("xyz", "abcdef");
  assert res == false;
}

method testIsSubstring3() {
  var res := isSubstring("", "hello");
  assert res == true;
}

method testHaveCommonKSubstring1() {
  var found := haveCommonKSubstring(2, "abcd", "bcde");
  assert found == true;
}

method testHaveCommonKSubstring2() {
  var found := haveCommonKSubstring(3, "abc", "xyz");
  assert found == false;
}

method testHaveCommonKSubstring3() {
  var found := haveCommonKSubstring(0, "abc", "xyz");
  assert found == true;
}

method testMaxCommonSubstringLength1() {
  var len := maxCommonSubstringLength("abc", "abcdef");
  assert len == 3;
}

method testMaxCommonSubstringLength2() {
  var len := maxCommonSubstringLength("xy", "abcdef");
  assert len == 0;
}

method testMaxCommonSubstringLength3() {
  var len := maxCommonSubstringLength("", "hello");
  assert len == 0;
}
