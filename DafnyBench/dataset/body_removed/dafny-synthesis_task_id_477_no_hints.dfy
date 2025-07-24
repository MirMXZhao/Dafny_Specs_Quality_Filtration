predicate IsUpperCase(c : char)
{}

predicate IsUpperLowerPair(C : char, c : char)
{}

function Shift32(c : char) :  char
{}

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{}