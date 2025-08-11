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
	ensures  res ==> isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str)
{}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{}

lemma commonKSubstringLemma(k:nat, str