method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
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



method TestMoveZeroesToEnd1() {
  var arr := new int[5];
  arr[0] := 0;
  arr[1] := 1;
  arr[2] := 0;
  arr[3] := 3;
  arr[4] := 12;
  MoveZeroesToEnd(arr);
  assert arr[0] == 1 || arr[0] == 3 || arr[0] == 12;
  assert arr[1] == 1 || arr[1] == 3 || arr[1] == 12;
  assert arr[2] == 1 || arr[2] == 3 || arr[2] == 12;
  assert arr[3] == 0;
  assert arr[4] == 0;
}

method TestMoveZeroesToEnd2() {
  var arr := new int[4];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  arr[3] := 4;
  MoveZeroesToEnd(arr);
  assert arr[0] == 1;
  assert arr[1] == 2;
  assert arr[2] == 3;
  assert arr[3] == 4;
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
  var arr := new int[4];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  arr[3] := 4;
  swap(arr, 1, 3);
  assert arr[0] == 1;
  assert arr[1] == 4;
  assert arr[2] == 3;
  assert arr[3] == 2;
}

method TestCount1() {
  var result := count([1, 2, 3, 2, 2], 2);
  assert result == 3;
}

method TestCount2() {
  var result := count([1, 3, 5, 7], 2);
  assert result == 0;
}
