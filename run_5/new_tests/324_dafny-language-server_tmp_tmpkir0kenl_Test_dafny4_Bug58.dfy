function M1(f:map<int, bool>, i:int):bool

function M2(f:map<int, bool>, i:int):bool
{}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
{
    assert f[i];
}

////////TESTS////////

method TestM11() {
  var f := map[1 := true, 2 := false, 3 := true];
  var result := M1(f, 2);
  assert result == false;
}

method TestM12() {
  var f := map[5 := true, 10 := false];
  var result := M1(f, 7);
  assert result == false;
}

method TestM21() {
  var f := map[1 := true, 2 := false];
  var result := M2(f, 1);
  assert result == M2(f, 1);
}

method TestM22() {
  var f := map[3 := false, 4 := true];
  var result := M2(f, 4);
  assert result == M2(f, 4);
}
