predicate isSorted(a: array<int>)
  reads a
{}

method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 3, 5, 7, 9;
  var index := binarySearch(a, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 2, 4, 6, 8;
  var index := binarySearch(a, 3);
  assert index == -1;
}
