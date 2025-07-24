// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Monadic Laws
// Niki Vazou and Rustan Leino
// 28 March 2016

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



method TestAppend1() {
  var xs := Cons(1, Cons(2, Nil));
  var ys := Cons(3, Cons(4, Nil));
  var result := append(xs, ys);
  assert result == Cons(1, Cons(2, Cons(3, Cons(4, Nil))));
}

method TestAppend2() {
  var xs := Nil;
  var ys := Cons(1, Cons(2, Nil));
  var result := append(xs, ys);
  assert result == Cons(1, Cons(2, Nil));
}

method TestBind1() {
  var xs := Cons(1, Cons(2, Nil));
  var f := x => Cons(x, Cons(x+1, Nil));
  var result := Bind(xs, f);
  assert result == Cons(1, Cons(2, Cons(2, Cons(3, Nil))));
}

method TestBind2() {
  var xs := Nil;
  var f := x => Cons(x, Nil);
  var result := Bind(xs, f);
  assert result == Nil;
}
