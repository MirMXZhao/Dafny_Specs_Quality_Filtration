function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{}

////////TESTS////////

method testbelow_zero1() {
  var ops := [1, 2, -4, 5];
  var result := below_zero(ops);
  assert result == true;
}

method testbelow_zero2() {
  var ops := [1, 2, 3, 1];
  var result := below_zero(ops);
  assert result == false;
}

method testbelow_zero3() {
  var ops := [];
  var result := below_zero(ops);
  assert result == false;
}

method testsum1() {
  var s := [1, 2, 3, 4];
  var result := sum(s, 2);
  assert result == 3;
}

method testsum2() {
  var s := [5, -2, 8];
  var result := sum(s, 0);
  assert result == 0;
}

method testsum3() {
  var s := [];
  var result := sum(s, 0);
  assert result == 0;
}
