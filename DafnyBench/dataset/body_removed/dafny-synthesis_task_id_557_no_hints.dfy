predicate IsLowerCase(c : char)
{}

predicate IsUpperCase(c : char)
{}

predicate IsLowerUpperPair(c : char, C : char)
{}

predicate IsUpperLowerPair(C : char, c : char)
{}

function ShiftMinus32(c : char) :  char
{}

function Shift32(c : char) :  char
{}

method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{}