datatype Nat = Zero | Succ(Pred: Nat)

lemma Disc(n: Nat)
ensures n.Succ? || n.Zero?
{
    //
}

lemma LPred(n: Nat)
ensures Succ(n).Pred == n
{
    //
}

function add(m: Nat, n: Nat) : Nat
decreases m
{}

lemma AddZero(m: Nat)
ensures add(m, Zero) == m
{
    //
}

lemma AddAssoc(m: Nat, n: Nat, p: Nat)
ensures add(m, add(n, p)) == add(add(m, n), p)
{
    //
}

lemma AddComm(m: Nat, n: Nat)
ensures add(m, n) == add(n, m)
{}

predicate lt(m: Nat, n: Nat)
{
    (m.Zero? && n.Succ?) ||
    (m.Succ? && n.Succ? && lt(m.Pred, n.Pred))
}

lemma LtTrans(m: Nat, n: Nat, p: Nat)
requires lt(m, n)
requires lt(n, p)
ensures lt(m, p)
{}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

lemma Disc2<T>(l: List<T>, a: T)
ensures Cons(a, l).head == a && Cons(a, l).tail == l
{
    //
}

function size<T>(l: List<T>): nat
{}

function app<T>(l1: List<T>, l2: List<T>) : List<T>
{}

lemma LenApp<T>(l1: List<T>, l2: List<T>)
ensures size(app(l1, l2)) == size(l1) + size(l2)
{
    //
}

function rev<T> (l: List<T>) : List<T>
{}

lemma AppNil<T>(l: List<T>)
ensures app(l, Nil) == l
{
    //
}

lemma LR1<T> (l: List<T>, x: T)
ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
{
    //
}

lemma RevRev<T>(l: List<T>)
ensures rev(rev(l)) == l
{}

////////TESTS////////

method TestDisc1() {
  var n := Zero;
  Disc(n);
  assert n.Succ? || n.Zero?;
}

method TestDisc2() {
  var n := Succ(Zero);
  Disc(n);
  assert n.Succ? || n.Zero?;
}

method TestLPred1() {
  var n := Zero;
  LPred(n);
  assert Succ(n).Pred == n;
}

method TestLPred2() {
  var n := Succ(Succ(Zero));
  LPred(n);
  assert Succ(n).Pred == n;
}

method TestAddZero1() {
  var m := Zero;
  AddZero(m);
  assert add(m, Zero) == m;
}

method TestAddZero2() {
  var m := Succ(Succ(Zero));
  AddZero(m);
  assert add(m, Zero) == m;
}

method TestAddAssoc1() {
  var m := Zero;
  var n := Zero;
  var p := Zero;
  AddAssoc(m, n, p);
  assert add(m, add(n, p)) == add(add(m, n), p);
}

method TestAddAssoc2() {
  var m := Succ(Zero);
  var n := Succ(Zero);
  var p := Succ(Zero);
  AddAssoc(m, n, p);
  assert add(m, add(n, p)) == add(add(m, n), p);
}

method TestAddComm1() {
  var m := Zero;
  var n := Zero;
  AddComm(m, n);
  assert add(m, n) == add(n, m);
}

method TestAddComm2() {
  var m := Succ(Zero);
  var n := Succ(Succ(Zero));
  AddComm(m, n);
  assert add(m, n) == add(n, m);
}

method TestLtTrans1() {
  var m := Zero;
  var n := Succ(Zero);
  var p := Succ(Succ(Zero));
  LtTrans(m, n, p);
  assert lt(m, p);
}

method TestLtTrans2() {
  var m := Succ(Zero);
  var n := Succ(Succ(Zero));
  var p := Succ(Succ(Succ(Zero)));
  LtTrans(m, n, p);
  assert lt(m, p);
}

method TestDisc21() {
  var l := Nil;
  var a := 5;
  Disc2(l, a);
  assert Cons(a, l).head == a && Cons(a, l).tail == l;
}

method TestDisc22() {
  var l := Cons(3, Nil);
  var a := 7;
  Disc2(l, a);
  assert Cons(a, l).head == a && Cons(a, l).tail == l;
}

method TestLenApp1() {
  var l1: List<int> := Nil;
  var l2: List<int> := Nil;
  LenApp(l1, l2);
  assert size(app(l1, l2)) == size(l1) + size(l2);
}

method TestLenApp2() {
  var l1: List<int> := Cons(1, Nil);
  var l2: List<int> := Cons(2, Nil);
  LenApp(l1, l2);
  assert size(app(l1, l2)) == size(l1) + size(l2);
}

method TestAppNil1() {
  var l: List<int> := Nil;
  AppNil(l);
  assert app(l, Nil) == l;
}

method TestAppNil2() {
  var l: List<int> := Cons(1, Cons(2, Nil));
  AppNil(l);
  assert app(l, Nil) == l;
}

method TestLR11() {
  var l: List<int> := Nil;
  var x := 5;
  LR1(l, x);
  assert rev(app(l, Cons(x, Nil))) == Cons(x, rev(l));
}

method TestLR12() {
  var l: List<int> := Cons(1, Cons(2, Nil));
  var x := 3;
  LR1(l, x);
  assert rev(app(l, Cons(x, Nil))) == Cons(x, rev(l));
}

method TestRevRev1() {
  var l: List<int> := Nil;
  RevRev(l);
  assert rev(rev(l)) == l;
}

method TestRevRev2() {
  var l: List<int> := Cons(1, Cons(2, Cons(3, Nil)));
  RevRev(l);
  assert rev(rev(l)) == l;
}
