function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{}

method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{}

////////TESTS////////

method Testsum1() {
  var s := new int[3];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  var a := sum(s);
  assert a == 6;
}

method Testsum2() {
  var s := new int[1];
  s[0] := 5;
  var a := sum(s);
  assert a == 5;
}
