function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{}

////////TESTS////////

method TestMax1() {
  var s := new nat[4];
  s[0] := 3;
  s[1] := 1;
  s[2] := 5;
  s[3] := 2;
  var a := max(s);
  assert a == 5;
}

method TestMax2() {
  var s := new nat[3];
  s[0] := 7;
  s[1] := 7;
  s[2] := 4;
  var a := max(s);
  assert a == 7;
}
