function fib(n: nat): nat
{}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
{
    // Change the method body to instead use c as described.
    // You will need to change both the initialization and the loop.
    var i: int := 0;
        b := 0;
    var c := 1;
    while i < n
    {}
}
