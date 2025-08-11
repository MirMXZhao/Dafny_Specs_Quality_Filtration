method Gauss(n:int) returns (sum:int)
requires n >= 0
ensures sum == n*(n+1)/2
{}

method sumOdds(n:nat) returns (sum:nat)
ensures sum == n*n;
{}