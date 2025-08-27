method GetEven(s: array<nat>) modifies s
ensures forall i :: 0 <= i < s.Length ==> 
								if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
								else s[i] == old(s[i])
{}

////////TESTS////////

method TestGetEven1() {
  var s := new nat[4];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  s[3] := 4;
  GetEven(s);
  assert s[0] == 2;
  assert s[1] == 2;
  assert s[2] == 4;
  assert s[3] == 4;
}

method TestGetEven2() {
  var s := new nat[3];
  s[0] := 6;
  s[1] := 8;
  s[2] := 10;
  GetEven(s);
  assert s[0] == 6;
  assert s[1] == 8;
  assert s[2] == 10;
}
