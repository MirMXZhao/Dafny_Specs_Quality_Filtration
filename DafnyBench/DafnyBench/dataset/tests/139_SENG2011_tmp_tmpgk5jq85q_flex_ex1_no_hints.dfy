function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{}

method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{}

////////TESTS////////

method testsumcheck1() {
  var s := new int[3];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  var result := sumcheck(s, 2);
  assert result == 3;
}

method testsumcheck2() {
  var s := new int[4];
  s[0] := 5;
  s[1] := -2;
  s[2] := 7;
  s[3] := 1;
  var result := sumcheck(s, 0);
  assert result == 0;
}

method testsumcheck3() {
  var s := new int[3];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  var result := sumcheck(s, 3);
  assert result == 6;
}

method testsum1() {
  var s := new int[3];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  var a := sum(s);
  assert a == 6;
}

method testsum2() {
  var s := new int[2];
  s[0] := -5;
  s[1] := 8;
  var a := sum(s);
  assert a == 3;
}

method testsum3() {
  var s := new int[1];
  s[0] := 42;
  var a := sum(s);
  assert a == 42;
}
