function exp(x:int, e:int):int
	requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{}

lemma   exp3_Lemma(n:int) 
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
{}

lemma  mult8_Lemma(n:int)
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
{}

