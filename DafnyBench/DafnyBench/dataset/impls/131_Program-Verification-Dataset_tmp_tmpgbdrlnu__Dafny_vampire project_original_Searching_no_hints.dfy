method Find(blood: array<int>, key: int) returns (index: int)
requires blood != null
ensures 0 <= index ==> index < blood.Length && blood[index] == key
ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
{
  index := 0;
  while index < blood.Length
    invariant 0 <= index <= blood.Length
    invariant forall k :: 0 <= k < index ==> blood[k] != key
  {
    if blood[index] == key {
      return;
    }
    index := index + 1;
  }
  index := -1;
}

method TestFind1() {
  var blood := new int[4];
  blood[0] := 10;
  blood[1] := 20;
  blood[2] := 30;
  blood[3] := 40;
  var index := Find(blood, 20);
  assert index == 1;
}

method TestFind2() {
  var blood := new int[3];
  blood[0] := 5;
  blood[1] := 15;
  blood[2] := 25;
  var index := Find(blood, 100);
  assert index < 0;
}