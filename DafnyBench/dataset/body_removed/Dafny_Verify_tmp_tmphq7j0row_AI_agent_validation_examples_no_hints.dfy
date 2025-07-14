function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}


// Original davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//     ensures y == Power(N)
// {}



// Fine_tuned davinci-003 completion:
// method ComputePower1(N: int) returns (y: nat) requires N >= 0
//     ensures y == Power(N)
// {}

method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{}

// Original davinci-003 completion:
// method Max(a: array<nat>) returns (m: int)
//     requires a.Length > 0
//     ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//     ensures exists i :: 0 <= i < a.Length && m == a[i] 
// {}

// Fine_tuned davinci-003 completion:
// method Max1(a: array<nat>) returns (m: int)
//     ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
//     ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
// {}

method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{}

// Original davinci-003 completion:
// method Cube(n: nat) returns (c: nat) 
//     ensures c == n * n * n
// {}

// Fine_tuned davinci-003 completion:
// method Cube1(n: nat) returns (c: nat) 
//     ensures c == n * n * n
// {}



method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{}

// Original davinci-003 completion:
// method IncrementMatrix(a: array2<int>)
//     modifies a
//     ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {}

// Fine_tuned davinci-003 completion:
// method IncrementMatrix1(a: array2<int>)
//     modifies a
//     ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
// {}

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{}

// Original davinci-003 completion:
// method CopyMatrix(src: array2, dst: array2)
//     requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//     modifies dst
//     ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
// {}

// Fine_tuned davinci-003 completion:
// method CopyMatrix1(src: array2, dst: array2)
//     requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
//     modifies dst
//     ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//     var m := 0;
//     while m != src.Length0
//         invariant 0 <= m <= src.Length0
//         invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
//     {}




method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{}

// Original davinci-003 completion:
// method DoubleArray(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {}

// Fine_tuned davinci-003 completion:
// method DoubleArray1(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {}

method RotateLeft(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{}

// Original davinci-003 completion:
// method RotateLeft(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
//     ensures a[a.Length -1] == old(a[0])
// {}

// Fine_tuned davinci-003 completion:
// method RotateLeft1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//     ensures a[a.Length -1] == old(a[0])
// {}

method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{}

// Original davinci-003 completion:
// method RotateRight(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
//     ensures a[0] == old(a[a.Length-1])
// {}

// Fine_tuned davinci-003 completion:
// method RotateRight1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)])
//     ensures a[0] == old(a[a.Length-1])
// {}
