// verifies
function expo(x:int, n:nat): int
requires n >= 0;
{}

lemma {:induction false} Expon23(n: nat)
requires n >= 0;
ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0;
{}

method check() {
}
