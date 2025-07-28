//https://numpy.org/doc/stable/reference/generated/numpy.histogram.html

//Compute the histogram of a dataset.

method histogram (data: array<real>, bins: array<real>) returns (hist: array<int>) 
    requires bins.Length >= 2; 
    requires forall i :: 1 <= i < bins.Length ==> bins[i] > bins[i-1];
    ensures hist.Length == bins.Length - 1;
    ensures forall j :: 0 <= j < data.Length
{}

method histogram_helper(data: array<real>, bins: array<real>, hist: array<int>, index: int)
    requires bins.Length >= 2; 
    requires forall i :: 1 <= i < bins.Length ==> bins[i] > bins[i-1];
    decreases 

{}