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

////////TESTS////////

method TestToUppercase1() {
  var s := "hello";
  var v := ToUppercase(s);
  assert |v| == 5;
  assert v == "HELLO";
}

method TestToUppercase2() {
  var s := "HeLLo123";
  var v := ToUppercase(s);
  assert |v| == 8;
  assert v == "HELLO123";
}

method TestToUppercase3() {
  var s := "";
  var v := ToUppercase(s);
  assert |v| == 0;
  assert v == "";
}

method TestIsLowerCase1() {
  var result := IsLowerCase('a');
  assert result == true;
}

method TestIsLowerCase2() {
  var result := IsLowerCase('A');
  assert result == false;
}

method TestIsLowerCase3() {
  var result := IsLowerCase('1');
  assert result == false;
}

method TestIsLowerUpperPair1() {
  var result := IsLowerUpperPair('a', 'A');
  assert result == true;
}

method TestIsLowerUpperPair2() {
  var result := IsLowerUpperPair('a', 'B');
  assert result == false;
}

method TestIsLowerUpperPair3() {
  var result := IsLowerUpperPair('A', 'A');
  assert result == false;
}

method TestShiftMinus32_1() {
  var result := ShiftMinus32('a');
  assert result == 'A';
}

method TestShiftMinus32_2() {
  var result := ShiftMinus32('z');
  assert result == 'Z';
}

method TestShiftMinus32_3() {
  var result := ShiftMinus32('m');
  assert result == 'M';
}
