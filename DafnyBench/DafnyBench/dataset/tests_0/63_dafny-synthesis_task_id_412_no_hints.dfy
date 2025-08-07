predicate IsEven(n: int)
{
    n % 2 == 0
}

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{}

////////TESTS////////

method TestIsEven1() {
    var result := IsEven(4);
    assert result == true;
}

method TestIsEven2() {
    var result := IsEven(3);
    assert result == false;
}

method TestRemoveOddNumbers1() {
    var arr := new int[5];
    arr[0] := 2;
    arr[1] := 3;
    arr[2] := 4;
    arr[3] := 5;
    arr[4] := 6;
    var evenList := RemoveOddNumbers(arr);
    assert evenList == [2, 4, 6];
}

method TestRemoveOddNumbers2() {
    var arr := new int[4];
    arr[0] := 1;
    arr[1] := 3;
    arr[2] := 5;
    arr[3] := 7;
    var evenList := RemoveOddNumbers(arr);
    assert evenList == [];
}

method TestRemoveOddNumbers3() {
    var arr := new int[0];
    var evenList := RemoveOddNumbers(arr);
    assert evenList == [];
}
