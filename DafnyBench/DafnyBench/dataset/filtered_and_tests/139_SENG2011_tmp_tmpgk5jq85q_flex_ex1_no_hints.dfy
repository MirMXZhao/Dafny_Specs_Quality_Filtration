// sums from index 0 -> i - 1
function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{}

// returns sum of array
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{}

method Main() {}




method TestSum1() {
  var s := new int[3];
  s[0] := 5;
  s[1] := -2;
  s[2] := 7;
  var a := sum(s);
  assert a == 10;
}

method TestSum2() {
  var s := new int[1];
  s[0] := 42;
  var a := sum(s);
  assert a == 42;
}
