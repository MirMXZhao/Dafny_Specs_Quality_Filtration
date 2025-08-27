method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more


method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x

method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y

function factorial(n:int):int
requires n>=0
{}

method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)

{}

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{}

method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{}

function sumSerie(n:int):int
requires n >=1 
{}

lemma {:induction false} Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{}

method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a

{}

////////TESTS////////

method TestMultipleReturns1() {
  var more, less := multipleReturns(5, 2);
  assert more > 5;
  assert less < 5;
}

method TestMultipleReturns2() {
  var more, less := multipleReturns(10, 3);
  assert more > 10;
  assert less < 10;
}

method TestMultipleReturns21() {
  var more, less := multipleReturns2(4, 1);
  assert more + less == 8;
}

method TestMultipleReturns22() {
  var more, less := multipleReturns2(7, 2);
  assert more + less == 14;
}

method TestMultipleReturns31() {
  var more, less := multipleReturns3(3, 2);
  assert more - less == 4;
}

method TestMultipleReturns32() {
  var more, less := multipleReturns3(5, 3);
  assert more - less == 6;
}

method TestComputeFact1() {
  var f := ComputeFact(3);
  assert f == factorial(3);
}

method TestComputeFact2() {
  var f := ComputeFact(5);
  assert f == factorial(5);
}

method TestComputeFact21() {
  var f := ComputeFact2(4);
  assert f == factorial(4);
}

method TestComputeFact22() {
  var f := ComputeFact2(0);
  assert f == factorial(0);
}

method TestSqare1() {
  var x := Sqare(3);
  assert x == 9;
}

method TestSqare2() {
  var x := Sqare(5);
  assert x == 25;
}

method TestSqare21() {
  var x := Sqare2(4);
  assert x == 16;
}

method TestSqare22() {
  var x := Sqare2(7);
  assert x == 49;
}
