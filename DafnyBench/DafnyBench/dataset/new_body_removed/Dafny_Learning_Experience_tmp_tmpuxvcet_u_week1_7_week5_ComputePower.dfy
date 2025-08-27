 function Power(n:nat):nat 
{}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2*n;
}

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
{}
