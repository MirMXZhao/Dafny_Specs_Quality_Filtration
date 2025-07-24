/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}

// A simple test case to make sure the specification is adequate.
method testPowerIter(){}

method testPowerOpt(){}


method testPowerIter() {
  var p := powerIter(2.0, 3);
  assert p == power(2.0, 3);
}

method testPowerOpt() {
  var p := powerOpt(3.0, 4);
  assert p == power(3.0, 4);
}
