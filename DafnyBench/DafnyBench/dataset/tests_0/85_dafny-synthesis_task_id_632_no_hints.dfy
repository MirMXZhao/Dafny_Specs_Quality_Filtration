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

////////TESTS////////

method TestMoveZeroesToEnd1() {
    var arr := new int[4];
    arr[0] := 0;
    arr[1] := 1;
    arr[2] := 0;
    arr[3] := 2;
    var oldArr := arr[..];
    MoveZeroesToEnd(arr);
    assert arr.Length == 4;
    assert multiset(arr[..]) == multiset(oldArr);
}

method TestMoveZeroesToEnd2() {
    var arr := new int[5];
    arr[0] := 3;
    arr[1] := 0;
    arr[2] := 4;
    arr[3] := 0;
    arr[4] := 5;
    var oldArr := arr[..];
    MoveZeroesToEnd(arr);
    assert arr.Length == 5;
    assert multiset(arr[..]) == multiset(oldArr);
}

method TestMoveZeroesToEnd3() {
    var arr := new int[3];
    arr[0] := 1;
    arr[1] := 2;
    arr[2] := 3;
    var oldArr := arr[..];
    MoveZeroesToEnd(arr);
    assert arr.Length == 3;
    assert multiset(arr[..]) == multiset(oldArr);
}

method Testswap1() {
    var arr := new int[3];
    arr[0] := 1;
    arr[1] := 2;
    arr[2] := 3;
    var oldArr := arr[..];
    swap(arr, 0, 2);
    assert arr[0] == 3 && arr[2] == 1;
    assert arr[1] == 2;
    assert multiset(arr[..]) == multiset(oldArr);
}

method Testswap2() {
    var arr := new int[2];
    arr[0] := 5;
    arr[1] := 10;
    var oldArr := arr[..];
    swap(arr, 0, 1);
    assert arr[0] == 10 && arr[1] == 5;
    assert multiset(arr[..]) == multiset(oldArr);
}

method Testswap3() {
    var arr := new int[4];
    arr[0] := 7;
    arr[1] := 8;
    arr[2] := 9;
    arr[3] := 10;
    var oldArr := arr[..];
    swap(arr, 1, 1);
    assert arr[1] == 8 && arr[1] == 8;
    assert multiset(arr[..]) == multiset(oldArr);
}

method Testcount1() {
    var result := count([1, 2, 3, 2, 2], 2);
    assert result == 3;
}

method Testcount2() {
    var result := count([0, 0, 0], 1);
    assert result == 0;
}

method Testcount3() {
    var result := count([], 5);
    assert result == 0;
}
