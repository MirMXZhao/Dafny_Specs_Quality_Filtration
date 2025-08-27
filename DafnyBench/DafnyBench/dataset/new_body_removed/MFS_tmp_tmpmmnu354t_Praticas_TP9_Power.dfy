/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
    ensures power(b, e1+e2) == power(b, e1) * power(b, e2)
{}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{}
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}

// A simple test case to make sure the specification is adequate.
method testPower() {}
