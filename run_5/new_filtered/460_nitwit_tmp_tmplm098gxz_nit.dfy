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