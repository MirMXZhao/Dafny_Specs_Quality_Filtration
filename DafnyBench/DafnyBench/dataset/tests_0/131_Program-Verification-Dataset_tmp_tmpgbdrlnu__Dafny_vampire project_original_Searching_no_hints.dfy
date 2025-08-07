method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{}

////////TESTS////////

method testFind1() {
  var blood := new int[4] [1, 3, 5, 7];
  var index := Find(blood, 5);
  assert index == 2;
}

method testFind2() {
  var blood := new int[3] [2, 4, 6];
  var index := Find(blood, 9);
  assert index < 0;
}

method testFind3() {
  var blood := new int[0];
  var index := Find(blood, 1);
  assert index < 0;
}

method testFind4() {
  var blood := new int[1] [42];
  var index := Find(blood, 42);
  assert index == 0;
}
