function power(x: real, n: nat) : real
{}

method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
    ensures power(b, e1+e2) == power(b, e1) * power(b, e2)
{}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{}

method powerOpt(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}