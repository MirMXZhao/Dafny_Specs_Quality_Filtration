/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {}

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    if n == 0 {}
    else if n == 1 {}
    else if n % 2 == 0 {
        productOfPowers(x,  n/2, n/2); // recall lemma
        var temp := powerDC(x, n/2);
        return temp * temp;
    }
    else {
        productOfPowers(x, (n-1)/2, (n-1)/2); // recall lemma  
        var temp := powerDC(x, (n-1)/2);
        return temp * temp * x;
    } 
}

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma {:induction a} productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ }


// A few test cases (checked statically by Dafny).
method testPowerDC() {}
