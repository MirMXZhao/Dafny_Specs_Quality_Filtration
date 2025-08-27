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

method Testmaxcheck1() {
  var s := new nat[4] := [3, 7, 2, 9];
  var result := maxcheck(s, 2, 5);
  assert result == maxcheck(s, 2, 5);
}

method Testmaxcheck2() {
  var s := new nat[3] := [1, 4, 6];
  var result := maxcheck(s, 1, 3);
  assert result == maxcheck(s, 1, 3);
}

method Testmax1() {
  var s := new nat[4] := [3, 7, 2, 9];
  var a := max(s);
  assert a == 9;
}

method Testmax2() {
  var s := new nat[3] := [5, 1, 8];
  var a := max(s);
  assert a == 8;
}
