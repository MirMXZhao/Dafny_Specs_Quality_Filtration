type T = int
predicate sorted(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{}

method binarySearch(a: array<T>, x: T) returns (index: int) 
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    ensures 0 <= index <= a.Length
    ensures index > 0 ==> a[index-1] <= x
    ensures index < a.Length ==> a[index] >= x
{}

////////TESTS////////

method TestBinarySearch1() {
  var a := new T[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 3, 5, 7, 9;
  var index := binarySearch(a, 5);
  assert index == 2;
}

method TestBinarySearch2() {
  var a := new T[4];
  a[0], a[1], a[2], a[3] := 2, 4, 6, 8;
  var index := binarySearch(a, 1);
  assert index == 0;
}

method TestBinarySearch3() {
  var a := new T[3];
  a[0], a[1], a[2] := 1, 3, 5;
  var index := binarySearch(a, 6);
  assert index == 3;
}

method TestSorted1() {
  var a := new T[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  var result := sorted(a, 4);
  assert result == true;
}

method TestSorted2() {
  var a := new T[3];
  a[0], a[1], a[2] := 3, 1, 2;
  var result := sorted(a, 3);
  assert result == false;
}
