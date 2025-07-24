predicate isPrefixPredicate(pre: string, str:string)
{}

method isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{}

predicate isSubstringPredicate (sub: string, str:string)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{}


method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{}


predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{}
