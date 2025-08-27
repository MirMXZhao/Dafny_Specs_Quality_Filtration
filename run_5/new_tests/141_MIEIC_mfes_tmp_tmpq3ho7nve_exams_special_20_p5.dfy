type T = int
predicate sorted(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
method binarySearch(a: array<T>, x: T) returns (index: int) 
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    ensures 0 <= index <= a.Length
    ensures index > 0 ==> a[index-1] <= x
    ensures index < a.Length ==> a[index] >= x
{}

////////TESTS////////

method testbinarySearch1() {
  var a := new int[4];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7;
  var index := binarySearch(a, 4);
  assert index == 2;
}

method testbinarySearch2() {
  var a := new int[3];
  a[0] := 2; a[1] := 4; a[2] := 6;
  var index := binarySearch(a, 1);
  assert index == 0;
}
