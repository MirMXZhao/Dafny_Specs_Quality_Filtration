function exp(x:int, e:int):int
    decreases e
	requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{}

lemma   exp3_Lemma(n:int) 
    decreases n
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
{}

lemma  mult8_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
{}

////////TESTS////////

method Testexp1() {
  var result := exp(2, 3);
  assert result == 8;
}

method Testexp2() {
  var result := exp(5, 0);
  assert result == 1;
}

method Testexp3_Lemma1() {
  exp3_Lemma(1);
  assert (exp(3,1)-1)%2 == 0;
}

method Testexp3_Lemma2() {
  exp3_Lemma(3);
  assert (exp(3,3)-1)%2 == 0;
}

method Testmult8_Lemma1() {
  mult8_Lemma(1);
  assert (exp(3,2*1) - 1)%8 == 0;
}

method Testmult8_Lemma2() {
  mult8_Lemma(2);
  assert (exp(3,2*2) - 1)%8 == 0;
}
