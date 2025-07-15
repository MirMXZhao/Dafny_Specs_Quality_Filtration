//IMPL LeftShift
method LeftShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] < 64
ensures res.Length == a.Length
requires forall i ::  0 <= i < a.Length ==> 0 <= a[i] <= 65535 &&  0 <= b[i] <= 15
ensures forall i :: 0 <= i < a.Length ==> res[i] == ((a[i] as bv16) << (b[i] as bv4)) as int
{
    /* code modified by LLM (iteration 4): initialized res array with proper length */
    res := new int[a.Length];
    
    var i := 0;
    /* code modified by LLM (iteration 4): added comprehensive loop invariants with explicit decreases clause */
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res.Length == a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == ((a[j] as bv16 ) << (b[j] as bv4)) as int
        decreases a.Length - i
    {
        /* code modified by LLM (iteration 4): perform left shift operation with bounds check */
        assert 0 <= i < a.Length;
        assert 0 <= i < b.Length;
        assert b[i] < 64;
        res[i] := ((a[i] as bv16 ) << (b[i] as bv4)) as int;
        i := i + 1;
    }
}