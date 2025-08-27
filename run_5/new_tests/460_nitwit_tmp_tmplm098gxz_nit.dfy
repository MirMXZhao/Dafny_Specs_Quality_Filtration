predicate valid_base(b : nat) {
  b >= 2
}

predicate nitness(b : nat, n : nat)
  requires (valid_base(b))
{
  0 <= n < b
}

method nit_increment(b : nat, n : nat) returns (sum : nat, carry : nat)
  requires (valid_base(b))
  requires (nitness(b, n))
  ensures (nitness(b, sum))
  ensures (nitness(b, carry))
{}

predicate is_max_nit(b : nat, q : nat) {
  q == b - 1
}

method max_nit(b: nat) returns (nmax : nat)
  requires (valid_base(b))
  ensures (nitness(b, nmax))
  ensures (is_max_nit(b, nmax))
{
  nmax := b - 1;
}

method nit_flip(b: nat, n : nat) returns (nf : nat)
  requires (valid_base(b))
  requires (nitness(b, n))
  ensures (nitness (b, nf))
{}

method nit_add(b : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  ensures  (carry == 0 || carry == 1)
{}

method nit_add_three(b : nat, c : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (c == 0 || c == 1)
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  ensures  (carry == 0 || carry == 1)
{}

predicate bibble(b : nat, a : seq<nat>)
{
  valid_base(b) && 
  |a| == 4 && 
  forall n :: n in a ==> nitness(b, n)
}

method bibble_add(b : nat, p : seq<nat>, q : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  requires (bibble(b, q))
  ensures  (bibble(b, r))
{}

method bibble_increment(b : nat, p : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, r))
{}

method bibble_flip(b : nat, p : seq<nat>) returns (fp : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, fp))
{}

method n_complement(b : nat, p : seq<nat>) returns (com : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, com))
{}

////////TESTS////////

method Testnit_increment1() {
  var sum, carry := nit_increment(10, 5);
  assert sum == 6;
  assert carry == 0;
}

method Testnit_increment2() {
  var sum, carry := nit_increment(2, 1);
  assert sum == 0;
  assert carry == 1;
}

method Testmax_nit1() {
  var nmax := max_nit(10);
  assert nmax == 9;
}

method Testmax_nit2() {
  var nmax := max_nit(2);
  assert nmax == 1;
}

method Testnit_flip1() {
  var nf := nit_flip(10, 3);
  assert nf == 6;
}

method Testnit_flip2() {
  var nf := nit_flip(2, 0);
  assert nf == 1;
}

method Testnit_add1() {
  var z, carry := nit_add(10, 3, 4);
  assert z == 7;
  assert carry == 0;
}

method Testnit_add2() {
  var z, carry := nit_add(10, 7, 8);
  assert z == 5;
  assert carry == 1;
}

method Testnit_add_three1() {
  var z, carry := nit_add_three(10, 1, 3, 4);
  assert z == 8;
  assert carry == 0;
}

method Testnit_add_three2() {
  var z, carry := nit_add_three(10, 1, 6, 7);
  assert z == 4;
  assert carry == 1;
}

method Testbibble_add1() {
  var r := bibble_add(10, [1, 2, 3, 4], [2, 3, 4, 5]);
  assert r == [3, 5, 7, 9];
}

method Testbibble_add2() {
  var r := bibble_add(10, [8, 9, 1, 2], [3, 2, 4, 5]);
  assert r == [1, 1, 5, 7];
}

method Testbibble_increment1() {
  var r := bibble_increment(10, [1, 2, 3, 4]);
  assert r == [1, 2, 3, 5];
}

method Testbibble_increment2() {
  var r := bibble_increment(10, [9, 9, 9, 9]);
  assert r == [0, 0, 0, 0];
}

method Testbibble_flip1() {
  var fp := bibble_flip(10, [1, 2, 3, 4]);
  assert fp == [8, 7, 6, 5];
}

method Testbibble_flip2() {
  var fp := bibble_flip(10, [0, 5, 9, 2]);
  assert fp == [9, 4, 0, 7];
}

method Testn_complement1() {
  var com := n_complement(10, [1, 2, 3, 4]);
  assert com == [8, 7, 6, 6];
}

method Testn_complement2() {
  var com := n_complement(10, [0, 0, 0, 0]);
  assert com == [0, 0, 0, 0];
}
