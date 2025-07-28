//https://numpy.org/doc/stable/reference/generated/numpy.convolve.html

//convolves two 1d arrays

method convolve (arr1: array<real>, arr2: array<real>) returns (ret: array<real>)
    requires arr1.Length > 0 && arr2.Length > 0
    ensures ret.Length == arr1.Length + arr2.Length - 1; 
    ensures forall n :: 0 <= n < ret.Length ==> ret[n] == (sum(arr1[i] * arr2[n - i], 0 , arr1.Length))
{}