//https://numpy.org/doc/stable/reference/generated/numpy.polyder.html

//Return the derivative of the specified order of a polynomial.
//the value of the poly[i] is the coefficient of x^i in the polynomial

method polyder (poly: array<real>, m: int) returns (ret: array<real>) //m is the order of the polynomial
    requires m > 0;
    ensures ret.Length == poly.Length - m 
    decreases m 
{
    assert forall i :: 0 < i < ret.Length ==> ret[i] == poly[i] * (i as real);
}