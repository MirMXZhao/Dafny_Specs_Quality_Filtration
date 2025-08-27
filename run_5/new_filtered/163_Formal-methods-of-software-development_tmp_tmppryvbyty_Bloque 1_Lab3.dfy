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