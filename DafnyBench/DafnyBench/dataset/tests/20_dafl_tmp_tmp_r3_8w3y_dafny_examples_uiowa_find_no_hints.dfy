method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;
   ensures 0 <= i ==> (i < a.Length && 
                       a[i] == key && 
                       forall k :: 0 <= k < i ==> a[k] != key
                      );
   ensures i < 0 ==> 
           forall k :: 0 <= k < a.Length ==> a[k] != key;
{}

////////TESTS////////

method TestFind1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 5;
  a[3] := 3;
  var i := Find(a, 3);
  assert i == 1;
}

method TestFind2() {
  var a := new int[3];
  a[0] := 2;
  a[1] := 4;
  a[2] := 6;
  var i := Find(a, 7);
  assert i < 0;
}

method TestFind3() {
  var a := new int[0];
  var i := Find(a, 5);
  assert i < 0;
}

method TestFind4() {
  var a := new int[1];
  a[0] := 42;
  var i := Find(a, 42);
  assert i == 0;
}
