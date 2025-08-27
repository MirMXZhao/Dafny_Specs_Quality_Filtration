method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
ensures b[..] == x[..] + y[..]

{}