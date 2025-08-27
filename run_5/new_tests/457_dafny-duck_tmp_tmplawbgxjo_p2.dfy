function abs(x:int):nat {}

method absx(x:array<int>) returns (y:array<int>) 
ensures y.Length == x.Length
ensures forall i :: 0 <= i < y.Length ==>  y[i] == abs(x[i])
{}

////////TESTS////////

method TestAbsx1() {
  var x := new int[4];
  x[0] := -5;
  x[1] := 3;
  x[2] := -2;
  x[3] := 7;
  var y := absx(x);
  assert y[0] == 5;
  assert y[1] == 3;
  assert y[2] == 2;
  assert y[3] == 7;
}

method TestAbsx2() {
  var x := new int[3];
  x[0] := 0;
  x[1] := -10;
  x[2] := 15;
  var y := absx(x);
  assert y[0] == 0;
  assert y[1] == 10;
  assert y[2] == 15;
}
