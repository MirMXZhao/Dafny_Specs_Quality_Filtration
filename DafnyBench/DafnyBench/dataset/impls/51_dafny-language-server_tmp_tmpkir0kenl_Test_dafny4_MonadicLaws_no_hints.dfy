datatype List<T> = Nil | Cons(head: T, tail: List)

function append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(head, tail) => Cons(head, append(tail, ys))
}

lemma AppendNil(xs: List)
  ensures append(xs, Nil) == xs
{
  match xs
  case Nil => 
  case Cons(head, tail) => AppendNil(tail);
}

lemma AppendAssoc(xs: List, ys: List, zs: List)
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
  match xs
  case Nil =>
  case Cons(head, tail) => AppendAssoc(tail, ys, zs);
}

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil => Nil
  case Cons(head, tail) => append(f(head), Bind(tail, f))
}


function Return<T>(a: T): List
{
  Cons(a, Nil)
}

lemma LeftIdentity<T>(a: T, f: T -> List)
  ensures Bind(Return(a), f) == f(a)
{
  AppendNil(f(a));
}

lemma RightIdentity<T>(m: List)
  ensures Bind(m, Return) == m
{
  match m
  case Nil =>
  case Cons(head, tail) => 
    RightIdentity(tail);
    AppendNil(Cons(head, tail));
}

lemma Associativity<T>(m: List, f: T -> List, g: T -> List)
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
{
  match m
  case Nil =>
  case Cons(head, tail) =>
    Associativity(tail, f, g);
    BindOverAppend(f(head), Bind(tail, f), g);
}

lemma BindOverAppend<T>(xs: List, ys: List, g: T -> List)
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{
  match xs
  case Nil =>
  case Cons(head, tail) =>
    BindOverAppend(tail, ys, g);
    AppendAssoc(g(head), Bind(tail, g), Bind(ys, g));
}

// method TestAppend1() {
//   var xs := Cons(1, Cons(2, Nil));
//   var ys := Cons(3, Cons(4, Nil));
//   var result := append(xs, ys);
//   assert result == Cons(1, Cons(2, Cons(3, Cons(4, Nil))));
// }

// method TestAppend2() {
//   var xs := Nil;
//   var ys := Cons(1, Cons(2, Nil));
//   var result := append(xs, ys);
//   assert result == Cons(1, Cons(2, Nil));
// }

// method TestBind1() {
//   var xs := Cons(1, Cons(2, Nil));
//   var f := x => Cons(x, Cons(x+1, Nil));
//   var result := Bind(xs, f);
//   assert result == Cons(1, Cons(2, Cons(2, Cons(3, Nil))));
// }

// method TestBind2() {
//   var xs := Nil;
//   var f := x => Cons(x, Nil);
//   var result := Bind(xs, f);
//   assert result == Nil;
// }