function Sum(arr: array<int>, len: int): int
    reads arr
    requires arr.Length > 0 && 0 <= len <= arr.Length
{}

method SumArray(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    ensures sum == Sum(arr, arr.Length)
{}
