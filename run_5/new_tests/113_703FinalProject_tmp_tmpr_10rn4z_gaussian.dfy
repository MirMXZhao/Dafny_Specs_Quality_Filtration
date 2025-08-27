method gaussian (size:int, q: array<real>, q_hat: array<real>) returns (out: array<real>)
requires q_hat.Length==size
requires q.Length==size
requires size > 0
requires arraySquaredSum(q_hat[..]) <= 1.0
{}


function arraySquaredSum(a: seq<real>): real
requires |a| > 0
{}

////////TESTS////////

method TestGaussian1() {
  var size := 3;
  var q := new real[3];
  q[0] := 0.5;
  q[1] := 0.3;
  q[2] := 0.2;
  var q_hat := new real[3];
  q_hat[0] := 0.4;
  q_hat[1] := 0.3;
  q_hat[2] := 0.2;
  var out := gaussian(size, q, q_hat);
  assert out.Length == 3;
}

method TestGaussian2() {
  var size := 2;
  var q := new real[2];
  q[0] := 1.0;
  q[1] := 0.5;
  var q_hat := new real[2];
  q_hat[0] := 0.6;
  q_hat[1] := 0.8;
  var out := gaussian(size, q, q_hat);
  assert out.Length == 2;
}
