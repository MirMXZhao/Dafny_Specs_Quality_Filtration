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
  var arr := new int[5];
  arr[0] := 1;
  arr[1] := 0;
  arr[2] := 3;
  arr[3] := 0;
  arr[4] := 5;
  MoveZeroesToEnd(arr);
  assert arr[0] == 1;
  assert arr[1] == 3;
  assert arr[2] == 5;
  assert arr[3] == 0;
  assert arr[4] == 0;
}

method TestMoveZeroesToEnd2() {
  var arr := new int[4];
  arr[0] := 2;
  arr[1] := 4;
  arr[2] := 6;
  arr[3] := 8;
  MoveZeroesToEnd(arr);
  assert arr[0] == 2;
  assert arr[1] == 4;
  assert arr[2] == 6;
  assert arr[3] == 8;
}

method TestSwap1() {
  var arr := new int[3];
  arr[0] := 10;
  arr[1] := 20;
  arr[2] := 30;
  swap(arr, 0, 2);
  assert arr[0] == 30;
  assert arr[1] == 20;
  assert arr[2] == 10;
}

method TestSwap2() {
  var arr := new int[2];
  arr[0] := 5;
  arr[1] := 7;
  swap(arr, 1, 0);
  assert arr[0] == 7;
  assert arr[1] == 5;
}

method TestCount1() {
  var arr := [1, 0, 1, 0, 1];
  var result := count(arr, 0);
  assert result == 2;
}

method TestCount2() {
  var arr := [5, 5, 5, 3, 3];
  var result := count(arr, 5);
  assert result == 3;
}
