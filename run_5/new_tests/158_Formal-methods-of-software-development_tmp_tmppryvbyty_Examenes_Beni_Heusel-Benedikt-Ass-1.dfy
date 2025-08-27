function exp (x:int,e:nat):int
{}

lemma div10_Lemma (n:nat)
requires n >= 3;
ensures (exp(3,4*n)+9)%10 == 0
{}

lemma div10Forall_Lemma ()
ensures forall n :: n>=3 ==> (exp(3,4*n)+9)%10==0
{}

function sumSerie (x:int,n:nat):int
{}

lemma  {:induction false} sumSerie_Lemma (x:int,n:nat)
ensures (1-x) * sumSerie(x,n) == 1 - exp(x,n+1)
{}

lemma notSq_Lemma (n:int)
ensures !exists z :: z*z == 4*n + 2
{}

lemma oneIsEven_Lemma (x:int,y:int,z:int)
requires z*z == x*x + y*y 
ensures x%2 == 0 || y%2 == 0
{}

lemma exp_Lemma(x:int, e:nat)			
requires x >= 1 
ensures exp(x,e) >= 1
{}

lemma prod_Lemma(z:int, a:int, b:int)
requires z >= 1 && a >= b >= 1
ensures  z*a >= z*b
{}

lemma expPlus1_Lemma(x:int,n:nat)
	requires x >= 1 && n >= 1
	ensures exp(x+1,n) >= exp(x,n) + 1 
   {}

////////TESTS////////

method TestExp1() {
  var result := exp(2, 3);
  assert result == 8;
}

method TestExp2() {
  var result := exp(5, 0);
  assert result == 1;
}

method TestSumSerie1() {
  var result := sumSerie(2, 3);
  assert result == 15;
}

method TestSumSerie2() {
  var result := sumSerie(1, 5);
  assert result == 6;
}
