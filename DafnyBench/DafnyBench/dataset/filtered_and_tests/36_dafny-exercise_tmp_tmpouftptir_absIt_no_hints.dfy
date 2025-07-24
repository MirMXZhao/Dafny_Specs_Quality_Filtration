method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{}

method Tester()
{}



method TestAbsIt1() {
  var s := new int[4];
  s[0] := -3;
  s[1] := 2;
  s[2] := -1;
  s[3] := 0;
  AbsIt(s);
  assert s[0] == 3;
  assert s[1] == 2;
  assert s[2] == 1;
  assert s[3] == 0;
}

method TestAbsIt2() {
  var s := new int[3];
  s[0] := 5;
  s[1] := -7;
  s[2] := 4;
  AbsIt(s);
  assert s[0] == 5;
  assert s[1] == 7;
  assert s[2] == 4;
}
