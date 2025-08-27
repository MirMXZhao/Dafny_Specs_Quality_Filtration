codatatype Conat = Zero | Succ(Pred: Conat)

greatest lemma ConstructorInjective(x: Conat, y: Conat)
    ensures Succ(x) == Succ(y) ==> x == y
{}

function inf(n: Conat): Conat
{
    Succ(inf(n))
}

function add(x: Conat, y: Conat) : Conat
{}

greatest predicate InfinityAddition()
{
    add(inf(Zero), inf(Zero)) == inf(Zero)
}

codatatype Stream<A> = Cons(head: A, tail: Stream<A>)

function addition(a: Stream<int>, b: Stream<int>): Stream<int>
{}

function cnst(a: int): Stream<int>
{}

greatest lemma additionWithZero(a : Stream<int>)
    ensures addition(a, cnst(0)) == a
{}

greatest predicate leq(a: Stream<int>, b: Stream<int>)
{ a.head <= b.head && ((a.head == b.head) ==> leq(a.tail, b.tail)) }

function blink(): Stream<int>
{}

lemma CnstZeroLeqBlink()
    ensures leq(cnst(0), blink())
{ 
}

function zip(a: Stream<int>, b: Stream<int>): Stream<int>
{}

greatest lemma ZipCnstZeroCnstOneEqualsBlink()
    ensures zip(cnst(0), cnst(1)) == blink()
{}

////////TESTS////////

method Testblink1() {
    var result := blink();
    assert result.head == 0 || result.head == 1;
}

method Testblink2() {
    var result := blink();
    assert result.tail.head == 0 || result.tail.head == 1;
}
