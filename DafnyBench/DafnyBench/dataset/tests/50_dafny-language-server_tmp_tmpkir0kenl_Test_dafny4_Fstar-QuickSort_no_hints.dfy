datatype List<T> = Nil | Cons(T, List)

function length(list: List): nat
{}

function In(x: int, list: List<int>): nat
{}

predicate SortedRange(m: int, n: int, list: List<int>)
{}

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
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
{}

////////TESTS////////

method testlength1() {
  var list := Cons(1, Cons(2, Cons(3, Nil)));
  var result := length(list);
  assert result == 3;
}

method testlength2() {
  var list := Nil;
  var result := length(list);
  assert result == 0;
}

method testlength3() {
  var list := Cons(10, Nil);
  var result := length(list);
  assert result == 1;
}

method testIn1() {
  var list := Cons(1, Cons(2, Cons(1, Nil)));
  var result := In(1, list);
  assert result == 2;
}

method testIn2() {
  var list := Cons(2, Cons(3, Cons(4, Nil)));
  var result := In(1, list);
  assert result == 0;
}

method testIn3() {
  var list := Nil;
  var result := In(5, list);
  assert result == 0;
}

method testappend1() {
  var i := Cons(1, Cons(2, Nil));
  var j := Cons(4, Cons(5, Nil));
  var result := append(1, 2, 4, 5, i, j);
  assert SortedRange(1, 5, result);
  assert forall x :: In(x, result) == In(x, i) + In(x, j);
}

method testappend2() {
  var i := Nil;
  var j := Cons(3, Nil);
  var result := append(1, 1, 3, 3, i, j);
  assert SortedRange(1, 3, result);
  assert forall x :: In(x, result) == In(x, i) + In(x, j);
}

method testappend3() {
  var i := Cons(2, Nil);
  var j := Nil;
  var result := append(2, 2, 5, 5, i, j);
  assert SortedRange(2, 5, result);
  assert forall x :: In(x, result) == In(x, i) + In(x, j);
}

method testpartition1() {
  var l := Cons(3, Cons(1, Cons(4, Cons(2, Nil))));
  var lo, hi := partition(2, l);
  assert forall y :: In(y, lo) == if y <= 2 then In(y, l) else 0;
  assert forall y :: In(y, hi) == if 2 < y then In(y, l) else 0;
  assert length(l) == length(lo) + length(hi);
}

method testpartition2() {
  var l := Cons(1, Cons(1, Nil));
  var lo, hi := partition(1, l);
  assert forall y :: In(y, lo) == if y <= 1 then In(y, l) else 0;
  assert forall y :: In(y, hi) == if 1 < y then In(y, l) else 0;
  assert length(l) == length(lo) + length(hi);
}

method testpartition3() {
  var l := Nil;
  var lo, hi := partition(0, l);
  assert forall y :: In(y, lo) == if y <= 0 then In(y, l) else 0;
  assert forall y :: In(y, hi) == if 0 < y then In(y, l) else 0;
  assert length(l) == length(lo) + length(hi);
}

method testsort1() {
  var i := Cons(3, Cons(1, Cons(2, Nil)));
  var result := sort(1, 3, i);
  assert SortedRange(1, 3, result);
  assert forall x :: In(x, i) == In(x, result);
}

method testsort2() {
  var i := Cons(5, Cons(5, Nil));
  var result := sort(5, 5, i);
  assert SortedRange(5, 5, result);
  assert forall x :: In(x, i) == In(x, result);
}

method testsort3() {
  var i := Nil;
  var result := sort(1, 10, i);
  assert SortedRange(1, 10, result);
  assert forall x :: In(x, i) == In(x, result);
}
