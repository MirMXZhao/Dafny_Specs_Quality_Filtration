

trait Comparable<T(==)> {
    function Lt(x: T, y: T): bool
}

  trait Sorted<T(==)> extends Comparable<T> {}

//   trait SelectionSort<T(==)> extends Comparable<T>, Sorted<T> {

//     method SelectionSort(a: array<T>)
//       modifies a
//       ensures Sorted(a)
//     {}

//   }

class Sort<T(==)> extends SelectionSort<T> {
    const CMP: (T,T) -> bool

    constructor(cmp: (T,T) -> bool)
      ensures CMP == cmp
      ensures comparisonCount == 0
    {}

    function Lt(x: T, y: T): bool {}
}

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
