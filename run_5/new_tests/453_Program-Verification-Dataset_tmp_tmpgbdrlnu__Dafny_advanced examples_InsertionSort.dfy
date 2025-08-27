predicate sorted (a:array<int>, start:int, end:int)      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {}


method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{}

////////TESTS////////

method TestInsertionSort1() {
  var a := new int[4];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 2;
  InsertionSort(a);
  assert sorted(a, 0, a.Length);
}

method TestInsertionSort2() {
  var a := new int[3];
  a[0] := 5; a[1] := 2; a[2] := 8;
  InsertionSort(a);
  assert sorted(a, 0, a.Length);
}
