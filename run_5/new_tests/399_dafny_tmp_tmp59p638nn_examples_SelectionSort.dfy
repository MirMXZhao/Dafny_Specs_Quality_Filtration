twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{}

////////TESTS////////

method TestSelectionSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  SelectionSort(a);
  assert Sorted(a);
}

method TestSelectionSort2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 2, 8;
  SelectionSort(a);
  assert Sorted(a);
}
