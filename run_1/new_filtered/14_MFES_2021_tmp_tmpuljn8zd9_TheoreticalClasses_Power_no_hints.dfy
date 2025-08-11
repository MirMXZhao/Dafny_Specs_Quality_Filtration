function power(x: real, n: nat) : real
{}

method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}