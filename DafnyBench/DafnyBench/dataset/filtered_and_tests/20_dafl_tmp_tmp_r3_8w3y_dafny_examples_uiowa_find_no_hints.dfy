/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/

method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;
   // if i is non-negative then 
   ensures 0 <= i ==> (// (1) i is smaller than the length of a
                       i < a.Length && 
                       // (2) key is at position i in a
                       a[i] == key && 
                       // (3) i is the smallest position where key appears
                       forall k :: 0 <= k < i ==> a[k] != key
                      );
   // if index is negative then
   ensures i < 0 ==> 
           // a does not contain key
           forall k :: 0 <= k < a.Length ==> a[k] != key;
{}




method TestFind1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 3, 7, 3;
  var i := Find(a, 3);
  assert i == 1;
}

method TestFind2() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 4;
  var i := Find(a, 9);
  assert i < 0;
}
