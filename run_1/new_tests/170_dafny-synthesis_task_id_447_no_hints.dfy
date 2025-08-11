method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures cubed.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{}

////////TESTS////////

method TestCubeElements1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var cubed := CubeElements(a);
  assert cubed[0] == 1;
  assert cubed[1] == 8;
  assert cubed[2] == 27;
  assert cubed[3] == 64;
}

method TestCubeElements2() {
  var a := new int[3];
  a[0] := -2; a[1] := 0; a[2] := 5;
  var cubed := CubeElements(a);
  assert cubed[0] == -8;
  assert cubed[1] == 0;
  assert cubed[2] == 125;
}
