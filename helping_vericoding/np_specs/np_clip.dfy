//https://numpy.org/doc/stable/reference/generated/numpy.clip.html

//Clip (limit) the values in an array
method clip (a: array<real>, min: real, max: real) returns (ret: array<real>)
    requires min < max;
    ensures ret.Length == a.Length;
    ensures forall i :: 0 <= i < a.Length ==> if a[i] < min then ret[i] == min else if a[i] > max then ret[i] == max else ret[i] == a[i];
{}