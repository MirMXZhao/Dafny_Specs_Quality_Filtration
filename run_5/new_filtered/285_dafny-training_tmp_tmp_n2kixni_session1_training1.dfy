method abs(x: int) returns (y: int)
    ensures true
{}

method foo(x: int) 
    requires x >= 0
{}

method max(x: int, y: int) returns (m: int)
requires true;
ensures true;
{}

method ex1(n: int)
    requires true
    ensures true
{}

method foo2() 
    ensures false
    decreases *
{}

method find(a: seq<int>, key: int) returns (index: int)
    requires true
    ensures true
{}

method isPalindrome(a: seq<char>) returns (b: bool) 
{
    return true;
}

predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures true
{
  return a;
}