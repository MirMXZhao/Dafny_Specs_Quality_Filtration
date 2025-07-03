//https://numpy.org/doc/stable/reference/generated/numpy.polyder.html

//Return the derivative of the specified order of a polynomial.

method polyder (poly: array<real>, m: int) returns (ret: array<real>) //m is the order of the polynomial
    requires m > 0;
    ensures ret.Length == poly.Length - m 
    ensures 
{}