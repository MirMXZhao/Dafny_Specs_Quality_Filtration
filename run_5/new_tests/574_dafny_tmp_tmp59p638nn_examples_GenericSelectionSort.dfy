trait Comparable<T(==)> {}

trait Sorted<T(==)> extends Comparable<T> {}

class Sort<T(==)> extends SelectionSort<T> {}

ghost function Sum(x: int): nat
{}

trait Measurable<T(==)> extends Comparable<T> {

    ghost var comparisonCount: nat

    method Ltm(x: T, y: T) returns (b: bool)
      modifies this`comparisonCount
      ensures b ==> Lt(x,y)
      ensures comparisonCount == old(comparisonCount) + 1
    {}

}

trait SelectionSort<T(==)> extends Comparable<T>, Measurable<T>, Sorted<T> {

    method SelectionSort(a: array<T>)
      modifies a, this
      requires comparisonCount == 0
      ensures Sorted(a)
      ensures comparisonCount <= a.Length * a.Length
    {}

}

////////TESTS////////

method TestSelectionSort1() {
  var s := new Sort<int>;
  var a := new int[3];
  a[0] := 3; a[1] := 1; a[2] := 2;
  s.SelectionSort(a);
  assert s.comparisonCount <= a.Length * a.Length;
}

method TestSelectionSort2() {
  var s := new Sort<int>;
  var a := new int[1];
  a[0] := 5;
  s.SelectionSort(a);
  assert s.comparisonCount <= a.Length * a.Length;
}
