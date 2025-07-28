//https://numpy.org/devdocs/reference/generated/numpy.unique_all.html

//Find the unique elements of an array, and counts, inverse, and indices.

method unique_all (arr: array<int>) returns (ret: array<int>)
    ensures ret.Length <= arr.Length;
    ensures forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i];
    ensures forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j]
{}