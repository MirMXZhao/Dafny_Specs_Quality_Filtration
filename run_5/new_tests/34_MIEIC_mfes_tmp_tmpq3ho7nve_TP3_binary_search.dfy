predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..]
{}

////////TESTS////////

method TestbinarySearch1() {
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  var index := binarySearch(a, 5);
  assert index == 2;
}

method TestbinarySearch2() {
  var a := new int[4];
  a[0] := 2; a[1] := 4; a[2] := 6; a[3] := 8;
  var index := binarySearch(a, 3);
  assert index == -1;
}
