function fact (n:nat): nat
 decreases n
{}

function factAcc (n:nat, a:int): int
 decreases n
{}

function factAlt(n:nat):int
{factAcc(n,1)}

lemma factAcc_correct (n:nat, a:int)
 ensures factAcc(n, a) == a*fact(n)
{
}

lemma factAlt_correct (n:nat)
 ensures factAlt(n) == fact(n)
{}

datatype List<T> = Nil | Cons(T, List<T>)

function length<T> (l: List<T>) : nat
decreases l
{}

lemma {:induction false} length_non_neg<T> (l:List<T>)
    ensures length(l) >= 0
{}

function lengthTL<T> (l: List<T>, acc: nat) : nat
{}

lemma {:induction false}lengthTL_aux<T> (l: List<T>, acc: nat)
    ensures lengthTL(l, acc) == acc + length(l)
{}

lemma lengthEq<T> (l: List<T>)
    ensures length(l) == lengthTL(l,0)
{}

////////TESTS////////

method TestFact1() {
  var result := fact(0);
  assert result == 1;
}

method TestFact2() {
  var result := fact(5);
  assert result == 120;
}

method TestFactAcc1() {
  var result := factAcc(0, 1);
  assert result == 1;
}

method TestFactAcc2() {
  var result := factAcc(4, 2);
  assert result == 48;
}

method TestFactAlt1() {
  var result := factAlt(0);
  assert result == 1;
}

method TestFactAlt2() {
  var result := factAlt(3);
  assert result == 6;
}

method TestLength1() {
  var result := length(Nil);
  assert result == 0;
}

method TestLength2() {
  var result := length(Cons(1, Cons(2, Cons(3, Nil))));
  assert result == 3;
}

method TestLengthTL1() {
  var result := lengthTL(Nil, 0);
  assert result == 0;
}

method TestLengthTL2() {
  var result := lengthTL(Cons(1, Cons(2, Nil)), 5);
  assert result == 7;
}
