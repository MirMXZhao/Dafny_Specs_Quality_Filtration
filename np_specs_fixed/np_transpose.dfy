method transpose(arr: array2<int>) returns (ret: array2<int>)
    ensures ret.Length0 == arr.Length1
    ensures ret.Length1 == arr.Length0
    ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> 
        ret[j, i] == arr[i, j]
{}