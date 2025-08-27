predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

////////TESTS////////

method TestMpositive1() {
  var v := new int[4];
  v[0] := 1; v[1] := 2; v[2] := 3; v[3] := 4;
  var b := mpositive(v);
  assert b == true;
}

method TestMpositive2() {
  var v := new int[3];
  v[0] := 1; v[1] := -2; v[2] := 3;
  var b := mpositive(v);
  assert b == false;
}

method TestMpositive31() {
  var v := new int[3];
  v[0] := 0; v[1] := 5; v[2] := 10;
  var b := mpositive3(v);
  assert b == true;
}

method TestMpositive32() {
  var v := new int[2];
  v[0] := -1; v[1] := 2;
  var b := mpositive3(v);
  assert b == false;
}

method TestMpositive41() {
  var v := new int[4];
  v[0] := 0; v[1] := 0; v[2] := 0; v[3] := 0;
  var b := mpositive4(v);
  assert b == true;
}

method TestMpositive42() {
  var v := new int[3];
  v[0] := 5; v[1] := 3; v[2] := -1;
  var b := mpositive4(v);
  assert b == false;
}

method TestMpositivertl1() {
  var v := new int[2];
  v[0] := 7; v[1] := 14;
  var b := mpositivertl(v);
  assert b == true;
}

method TestMpositivertl2() {
  var v := new int[4];
  v[0] := 3; v[1] := -5; v[2] := 2; v[3] := 8;
  var b := mpositivertl(v);
  assert b == false;
}
