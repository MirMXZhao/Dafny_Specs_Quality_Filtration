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
  arr[0], arr[1], arr[2], arr[3], arr[4] := 0, 1, 0, 3, 0;
  MoveZeroesToEnd(arr);
  assert arr[0] == 1 && arr[1] == 3 && arr[2] == 0 && arr[3] == 0 && arr[4] == 0;
}

method TestMoveZeroesToEnd2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 1, 2, 3, 4;
  MoveZeroesToEnd(arr);
  assert arr[0] == 1 && arr[1] == 2 && arr[2] == 3 && arr[3] == 4;
}

method TestSwap1() {
  var arr := new int[3];
  arr[0], arr[1], arr[2] := 1, 2, 3;
  swap(arr, 0, 2);
  assert arr[0] == 3 && arr[1] == 2 && arr[2] == 1;
}

method TestSwap2() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 5, 7, 9, 11;
  swap(arr, 1, 3);
  assert arr[0] == 5 && arr[1] == 11 && arr[2] == 9 && arr[3] == 7;
}

method TestCount1() {
  var arr := [1, 2, 3, 2, 2, 4];
  var result := count(arr, 2);
  assert result == 3;
}

method TestCount2() {
  var arr := [5, 6, 7, 8, 9];
  var result := count(arr, 10);
