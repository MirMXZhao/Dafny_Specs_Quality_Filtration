method factImp(n: int) returns (r: int)
{}

function power(n: int, m: nat) : int {}

function pow(n: int, m: nat,r: int) : int {}

function powerAlt(n: int,m: nat) : int {
  pow(n,m,1)
}

function equivalentes(n: int,m: nat,r: int) : int
  ensures power(n,m) == pow(n,m,r)

lemma l1(n: int,m: nat, r: int)
  ensures equivalentes(n,m, r) == powerAlt(n,m)

function fact(n: nat) : nat
{}

function factAcc(n: nat,a: int) : int
  decreases n
{}

function factAlt(n: nat) : int { factAcc(n,1) }

lemma factAcc_correct(n: nat,a: int)
  ensures factAcc(n,a) == fact(n)*a

lemma equiv(n: nat)
  ensures fact(n) == factAlt(n) {}

function mystery1(n: nat,m: nat) : nat
  decreases n, m;
  ensures mystery1(n,m) == n+m
{}

function mystery2(n: nat,m: nat) : nat
  decreases m
  ensures mystery2(n,m) == n+m
{}

function mystery3(n: nat,m: nat) : nat
  ensures mystery3(n,m) == n*m
{}

function mystery4(n: nat,m: nat) : nat
  ensures mystery4(n,m) == power(n,m)
{}