// RUN: /compile:0 /nologo

function IsEven(a : int) : bool
    requires a >= 0
{}

lemma EvenSquare(a : int)
requires a >= 0
ensures IsEven(a) ==> IsEven(a * a)
{}

lemma EvenDouble(a: int)
    requires a >= 0
    ensures IsEven(a + a)
{}

lemma {:induction x} EvenPlus(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x + y)
{}


/*
lemma {:induction x} EvenTimes(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x * y)
{}
*/

