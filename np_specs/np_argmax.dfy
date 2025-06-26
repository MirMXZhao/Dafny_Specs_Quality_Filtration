//https://numpy.org/doc/stable/reference/generated/numpy.argmax.html

//Returns the indices of the maximum values along an axis.
method argmax (arr: array<real>) returns (ret: nat)
    requires arr.Length > 0;
    ensures ret < arr.Length;
    ensures forall i :: 0 <= i < ret ==> arr[ret] > arr[i];
    ensures forall i :: ret < i < arr.Length ==> arr[ret] >= arr[i]
{} 