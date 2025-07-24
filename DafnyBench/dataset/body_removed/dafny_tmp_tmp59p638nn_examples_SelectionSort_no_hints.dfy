
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
{}

method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{}

 method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
  {}
