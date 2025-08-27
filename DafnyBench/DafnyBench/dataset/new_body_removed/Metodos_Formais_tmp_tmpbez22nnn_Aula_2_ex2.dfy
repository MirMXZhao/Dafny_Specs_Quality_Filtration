function Potencia(x: nat, y: nat): nat
{}

method Pot(x: nat, y: nat) returns (r: nat)
ensures r == Potencia(x,y)
{}
