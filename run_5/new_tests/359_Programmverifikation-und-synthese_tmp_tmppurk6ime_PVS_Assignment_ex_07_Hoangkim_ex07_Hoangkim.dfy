method swap(a: array<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{}

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{}

ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

method selectionSort(a: array<int>)
    modifies a
{}

////////TESTS////////

method TestSwap1() {
  var a := new int[4];
  a[0] := 10; a[1] := 20; a[2] := 30; a[3] := 40;
  swap(a, 1, 3);
  assert a[1] == 40;
  assert a[3] == 20;
}

method TestSwap2() {
  var a := new int[3];
  a[0] := 5; a[1] := 15; a[2] := 25;
  swap(a, 0, 2);
  assert a[0] == 25;
  assert a[2] == 5;
}

method TestFindMin1() {
  var a := new int[5];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 0; a[4] := 2;
  var minIdx := FindMin(a, 0);
  assert minIdx == 3;
}

method TestFindMin2() {
  var a := new int[4];
  a[0] := 7; a[1] := 2; a[2] := 9; a[3] := 5;
  var minIdx := FindMin(a, 1);
  assert minIdx == 1;
}

method TestSelectionSort1() {
  var a := new int[3];
  a[0] := 3; a[1] := 1; a[2] := 2;
  selectionSort(a);
}

method TestSelectionSort2() {
  var a := new int[4];
  a[0] := 5; a[1] := 2; a[2] := 8; a[3] := 1;
  selectionSort(a);
}
