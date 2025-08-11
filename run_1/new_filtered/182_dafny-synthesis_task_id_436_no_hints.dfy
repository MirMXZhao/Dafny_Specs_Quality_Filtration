predicate IsNegative(n: int)
{
    n < 0
}

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{}