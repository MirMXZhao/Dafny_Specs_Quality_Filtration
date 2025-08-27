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
    decreases b
{}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    decreases b
    ensures gcd(a,b) == r
{}

////////TESTS////////

method TestGCD11() {
  var r := GCD1(12, 8);
  assert r == 4;
}

method TestGCD12() {
  var r := GCD1(15, 10);
  assert r == 5;
}

method TestGCD21() {
  var r := GCD2(21, 14);
  assert r == 7;
}

method TestGCD22() {
  var r := GCD2(9, 0);
  assert r == 9;
}
