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