
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{}





