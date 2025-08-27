predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}

method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
{}

////////TESTS////////

method TestBinSearch1() {
  var a := new int[5] [1, 3, 5, 7, 9];
  var b := binSearch(a, 5);
  assert b == true;
}

method TestBinSearch2() {
  var a := new int[4] [2, 4, 6, 8];
  var b := binSearch(a, 3);
  assert b == false;
}
