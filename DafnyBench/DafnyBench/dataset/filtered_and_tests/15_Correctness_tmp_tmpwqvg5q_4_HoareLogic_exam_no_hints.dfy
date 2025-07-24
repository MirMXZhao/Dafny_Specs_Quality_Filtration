// Redo for exam

function gcd(a: nat, b: nat): nat

lemma r1(a: nat)
    ensures gcd(a, 0) == a

lemma r2(a:nat)
    ensures gcd(a, a) == a

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
{}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    ensures gcd(a,b) == r
{}


method TestGCD1_Case1() {
  var r := GCD1(12, 8);
  assert r == gcd(12, 8);
}

method TestGCD1_Case2() {
  var r := GCD1(15, 25);
  assert r == gcd(15, 25);
}

method TestGCD2_Case1() {
  var r := GCD2(10, 15);
  assert r == gcd(10, 15);
}

method TestGCD2_Case2() {
  var r := GCD2(7, 0);
  assert r == gcd(7, 0);
}
