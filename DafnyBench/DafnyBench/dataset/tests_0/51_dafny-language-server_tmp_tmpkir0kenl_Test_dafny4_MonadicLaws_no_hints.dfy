datatype List<T> = Nil | Cons(head: T, tail: List)

function append(xs: List, ys: List): List
{}

lemma AppendNil(xs: List)
  ensures append(xs, Nil) == xs
{
}

lemma AppendAssoc(xs: List, ys: List, zs: List)
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
}

function Return<T>(a: T): List
{
  Cons(a, Nil)
}

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
{}

lemma LeftIdentity<T>(a: T, f: T -> List)
  ensures Bind(Return(a), f) == f(a)
{}

lemma RightIdentity<T>(m: List)
  ensures Bind(m, Return) == m
{}

lemma Associativity<T>(m: List, f: T -> List, g: T -> List)
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
{}

lemma BindOverAppend<T>(xs: List, ys: List, g: T -> List)
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{}

////////TESTS////////

method testappend1() {
  var result := append(Cons(1, Nil), Cons(2, Nil));
  assert result == Cons(1, Cons(2, Nil));
}

method testappend2() {
  var result := append(Nil, Cons(3, Cons(4, Nil)));
  assert result == Cons(3, Cons(4, Nil));
}

method testappend3() {
  var result := append(Nil, Nil);
  assert result == Nil;
}

method testReturn1() {
  var result := Return(5);
  assert result == Cons(5, Nil);
}

method testReturn2() {
  var result := Return("hello");
  assert result == Cons("hello", Nil);
}

method testReturn3() {
  var result := Return(true);
  assert result == Cons(true, Nil);
}

method testBind1() {
  var xs := Cons(1, Cons(2, Nil));
  var f := x => Cons(x + 10, Nil);
  var result := Bind(xs, f);
  assert result == Cons(11, Cons(12, Nil));
}

method testBind2() {
  var xs := Nil;
  var f := x => Cons(x * 2, Nil);
  var result := Bind(xs, f);
  assert result == Nil;
}

method testBind3() {
  var xs := Cons(1, Nil);
  var f := x => Cons(x, Cons(x + 1, Nil));
  var result := Bind(xs, f);
  assert result == Cons(1, Cons(2, Nil));
}
