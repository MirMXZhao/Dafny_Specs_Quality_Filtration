method SquareElements(a: array<int>) returns (squared: array<int>)
    ensures squared.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
{}

////////TESTS////////

method TestSquareElements1() {
  var a := new int[4];
  a[0] := 1; a[1] := -2; a[2] := 3; a[3] := 0;
  var squared := SquareElements(a);
  assert squared[0] == 1;
  assert squared[1] == 4;
  assert squared[2] == 9;
  assert squared[3] == 0;
}

method TestSquareElements2() {
  var a := new int[3];
  a[0] := -5; a[1] := 4; a[2] := -1;
  var squared := SquareElements(a);
  assert squared[0] == 25;
  assert squared[1] == 16;
  assert squared[2] == 1;
}
