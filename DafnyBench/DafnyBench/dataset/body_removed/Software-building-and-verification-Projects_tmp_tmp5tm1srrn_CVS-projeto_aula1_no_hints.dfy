method factImp(n: int) returns (r: int)
{}

function power(n: int, m: nat) : int {}

function pow(n: int, m: nat,r: int) : int {}

function powerAlt(n: int,m: nat) : int {
  pow(n,m,1)
}

// 3

function equivalentes(n: int,m: nat,r: int) : int
  ensures power(n,m) == pow(n,m,r)

lemma l1(n: int,m: nat, r: int)
  ensures equivalentes(n,m, r) == powerAlt(n,m)


// 4.

function fact(n: nat) : nat
{}

function factAcc(n: nat,a: int) : int
{}

function factAlt(n: nat) : int { factAcc(n,1) }

lemma factAcc_correct(n: nat,a: int)
  ensures factAcc(n,a) == fact(n)*a

lemma equiv(n: nat)
  ensures fact(n) == factAlt(n) {}

// 5. a)
function mystery1(n: nat,m: nat) : nat
  ensures mystery1(n,m) == n+m
{}


// 5. b)
function mystery2(n: nat,m: nat) : nat
  ensures mystery2(n,m) == n+m
{}

// 5. c)
function mystery3(n: nat,m: nat) : nat
  ensures mystery3(n,m) == n*m
{}

// 5. d)
function mystery4(n: nat,m: nat) : nat
  ensures mystery4(n,m) == power(n,m)
{}

// 6

// 8

// 9

// 10

// 11
