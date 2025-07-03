//https://numpy.org/doc/stable/reference/generated/numpy.shape.html

//Return the shape of an array.

//testing allowing it to be multiple different array sizes
datatype arrays = arrayOne(arr1: array<real>) | arrayTwo(arr2: array2<real>) | arrayThree(arr3: array3<real>) 

method shape''(a: arrays) returns (ret: array<int>)
    ensures match a
              case arrayOne(arr1) => ret.Length == 1 && ret[0] == arr1.Length
              case arrayTwo(arr2) => ret.Length == 2 && ret[0] == arr2.Length0 && ret[1] == arr2.Length1
              case arrayThree(arr3) => ret.Length == 3 && ret[0] == arr3.Length0 && ret[1] == arr3.Length1 && ret[2] == arr3.Length2
{}

// method shape'<T> (a: arrays) returns (ret: array<int>)

//     ensures match a case arrayOne => ret.Length == 1 case arrayTwo => ret.Length == 2 case arrayThree => ret.Length == 3;
//     ensures match a case arrayOne => ret[0] == a.arr1.Length case arrayTwo => ret[0] ==a.arr2.Length0 case arrayThree => ret[0] ==a.arr3.Length0;
//     ensures match a case arrayTwo => ret[1] ==a.arr2.Length1 case arrayThree => ret[1] ==a.arr3.Length1;
//     ensures match a case arrayThree => ret[2] ==a.arr3.Length2;
// {}

method shape(a: array2<real>) returns (ret: array<int>)
    ensures ret.Length == 2
    ensures ret[0] == a.Length0 && ret[1] == a.Length1;
{}
