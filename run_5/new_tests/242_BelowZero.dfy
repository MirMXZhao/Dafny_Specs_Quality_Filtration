function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
}

method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{}

////////TESTS////////

method TestBelowZero1() {
  var ops := [1, 2, -4, 5];
  var result := BelowZero(ops);
  assert result == true;
}

method TestBelowZero2() {
  var ops := [1, 2, 3, 1];
  var result := BelowZero(ops);
  assert result == false;
}
