method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
ensures b[..] == x[..] + y[..]

{}

////////TESTS////////

method Testsingle1() {
  var x := new int[3];
  x[0] := 1; x[1] := 2; x[2] := 3;
  var y := new int[2];
  y[0] := 4; y[1] := 5;
  var b := single(x, y);
  assert b[..] == [1, 2, 3, 4, 5];
}

method Testsingle2() {
  var x := new int[1];
  x[0] := 10;
  var y := new int[3];
  y[0] := 20; y[1] := 30; y[2] := 40;
  var b := single(x, y);
  assert b[..] == [10, 20, 30, 40];
}
