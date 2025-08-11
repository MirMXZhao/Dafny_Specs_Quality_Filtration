method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
{}

////////TESTS////////

method TestDoubleArrayElements1() {
  var s := new int[4];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  s[3] := 4;
  double_array_elements(s);
  assert s[0] == 2;
  assert s[1] == 4;
  assert s[2] == 6;
  assert s[3] == 8;
}

method TestDoubleArrayElements2() {
  var s := new int[3];
  s[0] := -1;
  s[1] := 0;
  s[2] := 5;
  double_array_elements(s);
  assert s[0] == -2;
  assert s[1] == 0;
  assert s[2] == 10;
}
