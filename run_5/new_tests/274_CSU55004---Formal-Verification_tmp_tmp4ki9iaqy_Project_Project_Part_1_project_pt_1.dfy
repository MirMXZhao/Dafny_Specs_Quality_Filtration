method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str|
{}

method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str|
{}

method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2|
{}

method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str1|
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
  var str := "hello world";
  var res := isPrefix(pre, str);
  assert res == false;
}

method TestisSubstring1() {
  var sub := "ell";
  var str := "hello";
  var res := isSubstring(sub, str);
  assert res == true;
}

method TestisSubstring2() {
  var sub := "xyz";
  var str := "hello";
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
  var str2 := "help";
  var len := maxCommonSubstringLength(str1, str2);
  assert len == 3;
}

method TestmaxCommonSubstringLength2() {
  var str1 := "abc";
  var str2 := "def";
  var len := maxCommonSubstringLength(str1, str2);
  assert len == 0;
}
