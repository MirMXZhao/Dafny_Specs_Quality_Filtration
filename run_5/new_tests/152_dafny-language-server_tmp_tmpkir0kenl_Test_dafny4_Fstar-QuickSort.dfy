// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(T, List)

function length(list: List): nat
{}

function In(x: int, list: List<int>): nat
{}

predicate SortedRange(m: int, n: int, list: List<int>)
  decreases list
{
  match list
  case Nil => m <= n
  case Cons(hd, tl) => m <= hd <= n && SortedRange(hd, n, tl)
}

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
  decreases i
{}

function partition(x: int, l: List<int>): (List<int>, List<int>)
  ensures var (lo, hi) := partition(x, l);
    (forall y :: In(y, lo) == if y <= x then In(y, l) else 0) &&
    (forall y :: In(y, hi) == if x < y then In(y, l) else 0) &&
    length(l) == length(lo) + length(hi)
{}

function sort(min: int, max: int, i: List<int>): List<int>
  requires min <= max
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures SortedRange(min, max, sort(min, max, i))
  ensures forall x :: In(x, i) == In(x, sort(min, max, i))
  decreases length(i)
{}

////////TESTS////////

method Testlength1() {
  var list := Cons(1, Cons(2, Cons(3, Nil)));
  var result := length(list);
  assert result == 3;
}

method Testlength2() {
  var list := Nil;
  var result := length(list);
  assert result == 0;
}

method TestIn1() {
  var list := Cons(1, Cons(2, Cons(1, Nil)));
  var result := In(1, list);
  assert result == 2;
}

method TestIn2() {
  var list := Cons(2, Cons(3, Cons(4, Nil)));
  var result := In(1, list);
  assert result == 0;
}

method Testappend1() {
  var i := Cons(1, Cons(2, Nil));
  var j := Cons(3, Cons(4, Nil));
  var result := append(1, 2, 3, 4, i, j);
  assert result == Cons(1, Cons(2, Cons(3, Cons(4, Nil))));
}

method Testappend2() {
  var i := Nil;
  var j := Cons(5, Nil);
  var result := append(1, 3, 5, 6, i, j);
  assert result == Cons(5, Nil);
}

method Testpartition1() {
  var l := Cons(1, Cons(3, Cons(2, Nil)));
  var lo, hi := partition(2, l);
  assert lo == Cons(1, Cons(2, Nil));
  assert hi == Cons(3, Nil);
}

method Testpartition2() {
  var l := Cons(5, Cons(1, Cons(4, Nil)));
  var lo, hi := partition(3, l);
  assert lo == Cons(1, Nil);
  assert hi == Cons(5, Cons(4, Nil));
}

method Testsort1() {
  var i := Cons(3, Cons(1, Cons(2, Nil)));
  var result := sort(1, 3, i);
  assert result == Cons(1, Cons(2, Cons(3, Nil)));
}

method Testsort2() {
  var i := Cons(5, Cons(5, Nil));
  var result := sort(2, 8, i);
  assert result == Cons(5, Cons(5, Nil));
}
