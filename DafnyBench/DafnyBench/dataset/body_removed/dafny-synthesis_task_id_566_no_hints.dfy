method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{}

//lemma DivIsZero()
//  ensures forall num, den : nat :: den >= 1 && num < den ==> num/den == 0

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{}

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{}


lemma InIntValues(n: nat)
  ensures 0 in IntValues(n)
  ensures n in IntValues(n)
  ensures n/10 in IntValues(n)
{}

// ghost function ValuesOfn(number: nat, ndigits: nat) : (r: seq<nat>)
// {}

ghost function IntValues(n: int) : (r: seq<int>)
  requires n >= 0
  ensures 0 in r
  ensures n in r
  ensures n/10 in r
  //    ensures forall p :: p in powersOfTen ==> n/p in r
{}

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{}

function NumberToSeq(number: int) : seq<int>
  requires number >= 0
{}

function Sum(digits: seq<int>) : int
{}

function SumDigits(n: nat) : nat
{}

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
{}

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{}