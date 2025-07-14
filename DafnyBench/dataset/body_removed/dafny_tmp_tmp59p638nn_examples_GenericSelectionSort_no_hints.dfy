

trait Comparable<T(==)> {}

  trait Sorted<T(==)> extends Comparable<T> {

    ghost predicate Ordered(a: array<T>, left: nat, right: nat)
      reads a
      requires left <= right <= a.Length
    {}

    twostate predicate Preserved(a: array<T>, left: nat, right: nat)
      reads a
      requires left <= right <= a.Length
    {}

    twostate predicate Sorted(a: array<T>)
      reads a
    {}

  }

//   trait SelectionSort<T(==)> extends Comparable<T>, Sorted<T> {}

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

method Main()
{}
