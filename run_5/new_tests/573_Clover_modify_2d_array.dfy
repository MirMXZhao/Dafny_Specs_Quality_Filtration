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
  var inner1 := new nat[3];
  inner1[0], inner1[1], inner1[2] := 1, 2, 3;
  var inner2 := new nat[2];
  inner2[0], inner2[1] := 4, 5;
  var arr := new array<nat>[2];
  arr[0], arr[1] := inner1, inner2;
  modify_array_element(arr, 0, 1, 10);
  assert arr[0][0] == 1;
  assert arr[0][1] == 10;
  assert arr[0][2] == 3;
  assert arr[1][0] == 4;
  assert arr[1][1] == 5;
}

method TestModifyArrayElement2() {
  var inner1 := new nat[2];
  inner1[0], inner1[1] := 7, 8;
  var inner2 := new nat[3];
  inner2[0], inner2[1], inner2[2] := 9, 10, 11;
  var arr := new array<nat>[2];
  arr[0], arr[1] := inner1, inner2;
  modify_array_element(arr, 1, 2, 20);
  assert arr[0][0] == 7;
  assert arr[0][1] == 8;
  assert arr[1][0] == 9;
  assert arr[1][1] == 10;
  assert arr[1][2] == 20;
}
