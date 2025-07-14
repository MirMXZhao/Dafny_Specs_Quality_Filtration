function Potencia(x:nat, y:nat):nat
{}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{}
/*
Inv = 
Pot(2,3)
Teste de mesa
x   y   b   e   r           Inv --> b^e * r = x^y
2   3   2   3   1           2^3 * 2^0 = 2^3
2   3   2   2   1*2         2^2 * 2^1 = 2^3
2   3   2   1   1*2*2       2^1 * 2^2 = 2^3
2   3   2   0   1*2*2*2     2^0 * 2^3 = 2^3
*/
