predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{}