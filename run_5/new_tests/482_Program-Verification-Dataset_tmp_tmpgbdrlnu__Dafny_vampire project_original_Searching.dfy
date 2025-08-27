method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{}

////////TESTS////////

method TestFind1() {
  var blood := new int[5];
  blood[0], blood[1], blood[2], blood[3], blood[4] := 10, 20, 30, 20, 40;
  var index := Find(blood, 20);
  assert index == 1;
}

method TestFind2() {
  var blood := new int[3];
  blood[0], blood[1], blood[2] := 5, 15, 25;
  var index := Find(blood, 10);
  assert index < 0;
}
