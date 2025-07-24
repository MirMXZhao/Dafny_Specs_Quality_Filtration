type T = int // for demo purposes, but could be another type
predicate sorted(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
method binarySearch(a: array<T>, x: T) returns (index: int) 
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    //ensures a[..] == old(a)[..]
    ensures 0 <= index <= a.Length
    //ensures forall i :: 0 <= i < index ==> a[i] <= x
    //ensures forall i :: index <= i < a.Length ==> a[i] >= x

    ensures index > 0 ==> a[index-1] <= x
    ensures index < a.Length ==> a[index] >= x
{}

// Simple test cases to check the post-condition
method testBinarySearch() {}



method TestBinarySearch1() {
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  var index := binarySearch(a, 4);
  assert 0 <= index <= a.Length;
  assert index > 0 ==> a[index-1] <= 4;
  assert index < a.Length ==> a[index] >= 4;
}

method TestBinarySearch2() {
  var a := new int[3];
  a[0] := 2; a[1] := 6; a[2] := 8;
  var index := binarySearch(a, 10);
  assert 0 <= index <= a.Length;
  assert index > 0 ==> a[index-1] <= 10;
  assert index < a.Length ==> a[index] >= 10;
}
