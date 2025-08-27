function sorted(s : seq<int>) : bool {}

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{}

method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a 
{}

method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
{}

method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  decreases r - l
{}

////////TESTS////////

method TestCopyArr1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
  var ret := copyArr(a, 1, 4);
  assert ret[..] == [2, 3, 4];
}

method TestCopyArr2() {
  var a := new int[3];
  a[0], a[1], a[2] := 10, 20, 30;
  var ret := copyArr(a, 0, 2);
  assert ret[..] == [10, 20];
}
