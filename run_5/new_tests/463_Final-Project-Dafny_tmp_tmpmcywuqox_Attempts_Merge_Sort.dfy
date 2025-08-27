method mergeSort(a: array<int>)
modifies a
{}

method merging(a: array<int>, low: int, medium: int, high: int)
requires 0 <= low <= medium <= high < a.Length
modifies a
{}

method sorting(a: array<int>, low: int, high: int)
requires 0 <= low && high < a.Length
decreases high-low
modifies a
{}

////////TESTS////////

method TestMergeSort1() {
  var a := new int[4];
  a[0] := 4; a[1] := 2; a[2] := 7; a[3] := 1;
  mergeSort(a);
}

method TestMergeSort2() {
  var a := new int[3];
  a[0] := 1; a[1] := 3; a[2] := 2;
  mergeSort(a);
}

method TestMerging1() {
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 2; a[3] := 4; a[4] := 5;
  merging(a, 0, 2, 3);
}

method TestMerging2() {
  var a := new int[6];
  a[0] := 2; a[1] := 5; a[2] := 8; a[3] := 1; a[4] := 3; a[5] := 9;
  merging(a, 1, 2, 4);
}

method TestSorting1() {
  var a := new int[4];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 2;
  sorting(a, 0, 3);
}

method TestSorting2() {
  var a := new int[3];
  a[0] := 5; a[1] := 2; a[2] := 8;
  sorting(a, 1, 2);
}
