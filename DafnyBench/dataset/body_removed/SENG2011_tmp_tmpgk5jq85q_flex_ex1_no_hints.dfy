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


