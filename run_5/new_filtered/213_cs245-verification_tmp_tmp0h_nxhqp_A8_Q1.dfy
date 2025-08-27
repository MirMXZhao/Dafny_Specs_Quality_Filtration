function power(a: int, n: int): int
  requires 0 <= n;
  decreases n;{}


method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
ensures z==power(x,y0);
{}