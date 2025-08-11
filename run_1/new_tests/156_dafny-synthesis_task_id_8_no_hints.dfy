method SquareElements(a: array<int>) returns (squared: array<int>)
    ensures squared.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
{}

////////TESTS////////

method TestSquareElements1() {
  var a := new int[4];
  a[0] := 2;
  a[1] := -3;
  a[2] := 0;
  a[3] := 5;
  var squared := SquareElements(a);
  assert squared[0] == 4;
  assert squared[1] == 9;
  assert squared[2] == 0;
  assert squared[3] == 25;
}

method TestSquareElements2() {
  var a := new int[3];
  a[0] := -1;
  a[1] := 4;
  a[2] := -2;
  var squared := SquareElements(a);
  assert squared[0] == 1;
  assert squared[1] == 16;
  assert squared[2] == 4;
}
