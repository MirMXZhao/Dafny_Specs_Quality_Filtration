method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{}

method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{}