//https://numpy.org/doc/2.1/reference/generated/numpy.piecewise.html

//Evaluate a piecewise-defined function. Given a set of conditions and 
//corresponding functions, evaluate each function on the input data wherever its condition is true.

method piecewise(x: array<real>, condlist: array<real -> bool>, funclist: array<real -> real>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length;
    ensures ret.Length == x.Length;
    ensures forall i, j :: 0 <= i < x.Length && 0 <= j < condlist.Length ==> if condlist[j](x[i]) then ret[i] == funclist[j](x[i]) else true;
{}