predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{}

method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{}

////////TESTS////////

method TestToLowercase1() {
  var s := "Hello World";
  var v := ToLowercase(s);
  assert v == "hello world";
}

method TestToLowercase2() {
  var s := "ABC123xyz";
  var v := ToLowercase(s);
  assert v == "abc123xyz";
}
