function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
{}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{}

method Checker() {}
