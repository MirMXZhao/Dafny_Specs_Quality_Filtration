lemma AppendOne<T>(q: seq<T>, n: nat)
	requires n < |q|
	ensures q[..n]+[q[n]] == q[..n+1]
{}

function RecursivePositiveProduct(q: seq<int>): int
	decreases |q|
{}

function RecursiveCount(key: int, q: seq<int>): int
	decreases |q|
{}

method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
	ensures prod == RecursivePositiveProduct(q)
	ensures count == RecursiveCount(key, q)
{}

function county(elem: int, key: int): int{}

function prody(elem: int): int{}

lemma Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
	requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
	ensures 0 <= i+1 <= |q| && county(q[i],key)+count == RecursiveCount(key, q[..i+1])
{}

lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
	requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
	ensures 0 <= i+1 <= |q| && prody(q[i])*prod == RecursivePositiveProduct(q[..i+1])
{}

lemma Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
	requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
	requires neg_of_guard: i >= |q|
	ensures count == RecursiveCount(key, q)
{}

lemma Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
	requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
	requires neg_of_guard: i >= |q|
	ensures prod == RecursivePositiveProduct(q)
{}

lemma KibutzLaw1(q: seq<int>,key: int,i: nat)
requires q != [] && i < |q|
ensures 		
	(if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
	else 0 + RecursiveCount(key, q[1..i+1]))
	== 
	(if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1])
{}

lemma {:verify true} KibutzLaw2(q: seq<int>)
requires q != [] 
ensures 		
	(if q[0] <= 0 then RecursivePositiveProduct(q[1..])
		else q[0] * RecursivePositiveProduct(q[1..]))
	== 
	(if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..])
{}
		
lemma AppendCount(key: int, q: seq<int>)
	requires q != [] 
	ensures RecursiveCount(key, q) == RecursiveCount(key,q[..|q|-1])+county(q[|q|-1], key)	
{}

lemma PrependProd(q: seq<int>)
	requires q != []
	ensures RecursivePositiveProduct(q) == prody(q[0])*RecursivePositiveProduct(q[1..])
{}

lemma AppendProd(q: seq<int>)
	requires q != [] 
	ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q|-1])*prody(q[|q|-1])	
{}

////////TESTS////////

method TestProdAndCount1() {
  var q := [2, -3, 4, 5];
  var key := 4;
  var prod, count := ProdAndCount(q, key);
  assert prod == RecursivePositiveProduct(q);
  assert count == RecursiveCount(key, q);
}

method TestProdAndCount2() {
  var q := [1, 0, -2, 3];
  var key := 0;
  var prod, count := ProdAndCount(q, key);
  assert prod == RecursivePositiveProduct(q);
  assert count == RecursiveCount(key, q);
}
