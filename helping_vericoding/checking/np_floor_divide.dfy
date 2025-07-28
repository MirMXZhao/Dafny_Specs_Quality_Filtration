method FloorDivide(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] != 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] / b[i]
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == a[j] / b[j]
    {
        res[i] := a[i] / b[i];
        i := i + 1;
    }
}

method Main()
{
    var a:= new int[7][1, 3, 5, 8, 200, 50, 20];
    var b:= new int [7][2, 2, 2, 3, 27, 12, 3];
    var c:= FloorDivide(a, b);
}