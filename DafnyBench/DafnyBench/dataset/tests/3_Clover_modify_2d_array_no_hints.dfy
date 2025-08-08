method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j:nat :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures  arr[index1][index2] == val
{}

////////TESTS////////

method TestModifyArrayElement1() {
  var arr1 := new nat[3];
  arr1[0] := 1; arr1[1] := 2; arr1[2] := 3;
  var arr2 := new nat[2];
  arr2[0] := 4; arr2[1] := 5;
  var arr3 := new nat[1];
  arr3[0] := 6;
  var arr := new array<nat>[3];
  arr[0] := arr1; arr[1] := arr2; arr[2] := arr3;
  modify_array_element(arr, 1, 0, 10);
  assert arr[0][0] == 1 && arr[0][1] == 2 && arr[0][2] == 3;
  assert arr[1][0] == 10 && arr[1][1] == 5;
  assert arr[2][0] == 6;
}

method TestModifyArrayElement2() {
  var arr1 := new nat[2];
  arr1[0] := 7; arr1[1] := 8;
  var arr2 := new nat[3];
  arr2[0] := 9; arr2[1] := 10; arr2[2] := 11;
  var arr := new array<nat>[2];
  arr[0] := arr1; arr[1] := arr2;
  modify_array_element(arr, 0, 1, 15);
  assert arr[0][0] == 7 && arr[0][1] == 15;
  assert arr[1][0] == 9 && arr[1][1] == 10 && arr[1][2] == 11;
}
