method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
{}

////////TESTS////////

method TestRotate1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var b := rotate(a, 2);
  assert b.Length == 4;
  assert b[0] == 3;
  assert b[1] == 4;
  assert b[2] == 1;
  assert b[3] == 2;
}

method TestRotate2() {
  var a := new int[3];
  a[0] := 5; a[1] := 6; a[2] := 7;
  var b := rotate(a, 0);
  assert b.Length == 3;
  assert b[0] == 5;
  assert b[1] == 6;
  assert b[2] == 7;
}

method TestRotate3() {
  var a := new int[1];
  a[0] := 42;
  var b := rotate(a, 5);
  assert b.Length == 1;
  assert b[0] == 42;
}

method TestRotate4() {
  var a := new int[0];
  var b := rotate(a, 3);
  assert b.Length == 0;
}
