method {:verify true} FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
	ensures forall i :: i in offsets ==> i + |pattern| <= |text|
	ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{}

function RecursiveSumDown(str: string): int
{}

function RecursiveSumUp(str: string): int
{}

lemma {:verify true}LemmaRabinKarp(t_sub:string, pattern:string, text_hash:int, pattern_hash:int)
    requires text_hash != pattern_hash
    requires pattern_hash == RecursiveSumDown(pattern)
    requires text_hash == RecursiveSumDown(t_sub)
    ensures t_sub[..] != pattern[..]
{}

lemma Lemma2Sides(text: string, pattern: string, i: nat, offsets: set<nat>)
	requires 0 <= i <= |text| - |pattern|
	requires (text[i..i+|pattern|] == pattern ==> i in offsets)
	requires (text[i..i+|pattern|] == pattern <== i in offsets)
	ensures (text[i..i+|pattern|] == pattern <==> i in offsets)
{}

lemma LemmaHashEqualty(text_hash : int, text: string, i: nat, old_text_hash: int, pattern: string)
requires 0 < i <= |text| - |pattern|
requires text_hash == old_text_hash - text[i - 1] as int + text[i - 1 + |pattern|] as int
requires  old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
ensures text_hash == RecursiveSumDown(text[i..i+|pattern|])
{}

lemma LemmaAddingOneIndex(str: string, i: nat, sum: int)
	requires 0 <= i < |str| && sum == RecursiveSumDown(str[..i])
	ensures 0 <= i+1 <= |str| && sum + str[i] as int == RecursiveSumDown(str[..i+1])
{}

lemma PrependSumUp(str: string)
	requires str != ""
	ensures RecursiveSumUp(str) == str[0] as int + RecursiveSumUp(str[1..])
{}

lemma EquivalentSumDefinitions(str: string)
	ensures RecursiveSumDown(str) == RecursiveSumUp(str)
{}