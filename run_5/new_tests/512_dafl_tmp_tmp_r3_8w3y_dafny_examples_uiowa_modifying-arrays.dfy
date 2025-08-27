method SetEndPoints(a: array<int>, left: int, right: int)
  requires a.Length != 0 
  modifies a 
{}


method Aliases(a: array<int>, b: array<int>) 
	requires a.Length >= b.Length > 100  
	modifies a 
{}


method NewArray() returns (a: array<int>) 
  ensures a.Length == 20 
  ensures fresh(a)
{} 		

method Caller() 
{}


method InitArray<T>(a: array<T>, d: T) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{}


method UpdateElements(a: array<int>) 
  requires a.Length == 10 
  modifies a 
  ensures old(a[4]) < a[4] 
  ensures a[6] <= old(a[6]) 
  ensures a[8] == old(a[8]) 
{}


method IncrementArray(a: array<int>) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{}


method CopyArray<T>(a: array<T>, b: array<T>) 
	  requires a.Length == b.Length 
	  modifies b 
	  ensures forall i :: 0 <= i < a.Length ==> b[i] == old(a[i])
	{}

////////TESTS////////

method TestSetEndPoints1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
  SetEndPoints(a, 0, 4);
}

method TestSetEndPoints2() {
  var a := new int[3];
  a[0], a[1], a[2] := 10, 20, 30;
  SetEndPoints(a, 1, 2);
}

method TestAliases1() {
  var a := new int[150];
  var b := new int[101];
  Aliases(a, b);
}

method TestAliases2() {
  var a := new int[200];
  var b := new int[120];
  Aliases(a, b);
}

method TestNewArray1() {
  var a := NewArray();
  assert a.Length == 20;
}

method TestNewArray2() {
  var a := NewArray();
  assert a.Length == 20;
}

method TestCaller1() {
  Caller();
}

method TestCaller2() {
  Caller();
}

method TestInitArray1() {
  var a := new int[5];
  InitArray(a, 7);
  assert a[0] == 7;
  assert a[1] == 7;
  assert a[2] == 7;
  assert a[3] == 7;
  assert a[4] == 7;
}

method TestInitArray2() {
  var a := new int[3];
  InitArray(a, -2);
  assert a[0] == -2;
  assert a[1] == -2;
  assert a[2] == -2;
}

method TestUpdateElements1() {
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 1, 2, 3, 4, 5, 6, 7, 8, 9, 10;
  var old4 := a[4];
  var old6 := a[6];
  var old8 := a[8];
  UpdateElements(a);
  assert old4 < a[4];
  assert a[6] <= old6;
  assert a[8] == old8;
}

method TestUpdateElements2() {
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 0, 1, 2, 3, 4, 5, 6, 7, 8, 9;
  var old4 := a[4];
  var old6 := a[6];
  var old8 := a[8];
  UpdateElements(a);
  assert old4 < a[4];
  assert a[6] <= old6;
  assert a[8] == old8;
}

method TestIncrementArray1() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var old0, old1, old2 := a[0], a[1], a[2];
  IncrementArray(a);
  assert a[0] == old0 + 1;
  assert a[1] == old1 + 1;
  assert a[2] == old2 + 1;
}

method TestIncrementArray2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := -1, 0, 5, 10;
  var old0, old1, old2, old3 := a[0], a[1], a[2], a[3];
  IncrementArray(a);
  assert a[0] == old0 + 1;
  assert a[1] == old1 + 1;
  assert a[2] == old2 + 1;
  assert a[3] == old3 + 1;
}

method TestCopyArray1() {
  var a := new int[3];
  var b := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var oldA0, oldA1, oldA2 := a[0], a[1], a[2];
  CopyArray(a, b);
  assert b[0] == oldA0;
  assert b[1] == oldA1;
  assert b[2] == oldA2;
}

method TestCopyArray2() {
  var a := new int[2];
  var b := new int[2];
  a[0], a[1] := 10, 20;
  var oldA0, oldA1 := a[0], a[1];
  CopyArray(a, b);
  assert b[0] == oldA0;
  assert b[1] == oldA1;
}
