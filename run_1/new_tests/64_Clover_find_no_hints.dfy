method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
{}

////////TESTS////////

method TestFind1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 10, 20, 30, 20, 40;
  var index := Find(a, 20);
  assert index == 1;
}

method TestFind2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 10, 15, 25;
  var index := Find(a, 30);
  assert index == -1;
}
