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
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 7, 2, 9, 7;
  var i := Find(a, 7);
  assert i == 1;
}

method TestFind2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 3, 5, 8;
  var i := Find(a, 4);
  assert i < 0;
}
