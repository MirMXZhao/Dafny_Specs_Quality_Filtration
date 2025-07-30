method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    ensures arr.Length == old(arr.Length)
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    ensures forall n, m :: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l :: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
{}

method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{}