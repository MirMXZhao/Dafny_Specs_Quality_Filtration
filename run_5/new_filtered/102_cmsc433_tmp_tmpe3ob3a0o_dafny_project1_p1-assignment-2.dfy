method PlusOne (x : int) returns (y : int)
    requires x >= 0
    ensures y > 0
{
    y := x+1;
}

method Swap (a : array?<int>, i : int, j : int)
    requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
{}

method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == n * d + r && 0 <= r < n
{}

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length && 
        forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
{}

method Euclid (m : int, n : int) returns (gcd : int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
    

method IsSorted (a : array<int>) returns (isSorted : bool)
    ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{}

method IsPrime (m : int) returns (isPrime : bool)
    requires m > 0
    ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0) 
{}

method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev)
{}

method NoDups (a : array<int>) returns (noDups : bool)
    requires forall j : int :: 0 < j < a.Length ==> a[j-1] <= a[j]
    ensures noDups <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] != a[j]
{}