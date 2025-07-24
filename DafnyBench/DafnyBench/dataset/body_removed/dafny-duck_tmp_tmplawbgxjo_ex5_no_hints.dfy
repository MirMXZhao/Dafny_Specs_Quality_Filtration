// program verifies
function expo(x:int, n:nat): int
{}

lemma {:induction false} Expon23(n: nat)
requires n >= 0
ensures ((expo(2,3*n) - expo(3,n)) % (2+3)) == 0
{}

        
