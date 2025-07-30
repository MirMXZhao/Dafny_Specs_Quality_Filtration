lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {}

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {}

method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
    {}