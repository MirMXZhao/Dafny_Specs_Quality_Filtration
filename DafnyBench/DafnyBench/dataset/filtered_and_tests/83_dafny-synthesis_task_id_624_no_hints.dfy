predicate IsLowerCase(c : char)
{}

predicate IsLowerUpperPair(c : char, C : char)
{}

function ShiftMinus32(c : char) :  char
{}

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{}


method TestToUppercase1() {
  var s := "hello";
  var v := ToUppercase(s);
  assert v == "HELLO";
}

method TestToUppercase2() {
  var s := "Hello123";
  var v := ToUppercase(s);
  assert v == "HELLO123";
}
