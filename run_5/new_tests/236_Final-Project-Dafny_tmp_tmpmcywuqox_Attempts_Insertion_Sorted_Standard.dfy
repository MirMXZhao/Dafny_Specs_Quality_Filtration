predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{}


method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
{}

////////TESTS////////

method TestSorting1() {
  var arr := new int[4];
  arr[0] := 3;
  arr[1] := 1;
  arr[2] := 4;
  arr[3] := 2;
  sorting(arr);
  assert InsertionSorted(arr, 0, arr.Length);
}

method TestSorting2() {
  var arr := new int[3];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  sorting(arr);
  assert InsertionSorted(arr, 0, arr.Length);
}
