method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
{}

////////TESTS////////

method TestFind1() {
  var a := new int[5] [10, 20, 30, 40, 50];
  var index := Find(a, 30);
  assert index == 2;
}

method TestFind2() {
  var a := new int[4] [1, 2, 3, 4];
  var index := Find(a, 7);
  assert index == -1;
}
