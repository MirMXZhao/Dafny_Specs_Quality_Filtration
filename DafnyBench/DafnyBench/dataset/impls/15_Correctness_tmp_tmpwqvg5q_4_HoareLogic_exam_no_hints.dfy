function gcd(a: nat, b: nat): nat
{
    if b == 0 then a else gcd(b, a % b)
}

lemma r1(a: nat)
    ensures gcd(a, 0) == a
{
}

lemma r2(a:nat)
    ensures gcd(a, a) == a
{
    if a == 0 {
    } else {
        assert a % a == 0;
        r1(a);
    }
}

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)
{
    if b == 0 {
        r1(a);
        r1(b);
    } else if a == 0 {
        r1(a);
        r1(b);
    } else {
        r3(b, a % b);
        r3(a % b, b);
    }
}

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)
{
}

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
{
    var x := a;
    var y := b;
    while y != 0
        invariant x > 0 && y >= 0
        invariant gcd(x, y) == gcd(a, b)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    r := x;
}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    ensures gcd(a,b) == r
{
    if b == 0 {
        r := a;
    } else {
        r := GCD1(a, b);
    }
}

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