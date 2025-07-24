// Ch. 8: Sorting

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{}

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{}

ghost predicate Ordered(xs: List<int>) {}

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{}

// Ex. 8.0 generalize fron int to T by: T(==)
ghost function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{}

ghost function Project<T(==)>(xs: List<T>, p: T): List<T> {}

// Ex 8.1
lemma {:induction false} CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  requires Project(xs, p) == Project(ys, p)
  ensures Count(xs, p) == Count(ys, p)
{}

function InsertionSort(xs: List<int>): List<int>
{}

function Insert(x: int, xs: List<int>): List<int>
{}

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{}


method TestCount1() {
  var xs := Cons(1, Cons(2, Cons(1, Cons(3, Nil))));
  var result := Count(xs, 1);
  assert result == 2;
}

method TestCount2() {
  var xs := Cons(5, Cons(5, Cons(5, Nil)));
  var result := Count(xs, 5);
  assert result == 3;
}

method TestProject1() {
  var xs := Cons(1, Cons(2, Cons(1, Cons(3, Nil))));
  var result := Project(xs, 1);
  assert result == Cons(1, Cons(1, Nil));
}

method TestProject2() {
  var xs := Cons(4, Cons(5, Cons(6, Nil)));
  var result := Project(xs, 7);
  assert result == Nil;
}

method TestInsertionSort1() {
  var xs := Cons(3, Cons(1, Cons(2, Nil)));
  var result := InsertionSort(xs);
  assert result == Cons(1, Cons(2, Cons(3, Nil)));
}

method TestInsertionSort2() {
  var xs := Cons(5, Nil);
  var result := InsertionSort(xs);
  assert result == Cons(5, Nil);
}

method TestInsert1() {
  var xs := Cons(1, Cons(3, Cons(5, Nil)));
  var result := Insert(2, xs);
  assert result == Cons(1, Cons(2, Cons(3, Cons(5, Nil))));
}

method TestInsert2() {
  var xs := Nil;
  var result := Insert(10, xs);
  assert result == Cons(10, Nil);
}
