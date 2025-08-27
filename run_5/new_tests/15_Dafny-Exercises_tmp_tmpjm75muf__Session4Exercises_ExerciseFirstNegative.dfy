predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}


method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
{}

method mfirstNegative2(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
{}

////////TESTS////////

method TestMfirstNegative1() {
  var v := new int[5];
  v[0] := 3;
  v[1] := 7;
  v[2] := -2;
  v[3] := 1;
  v[4] := 5;
  var b, i := mfirstNegative(v);
  assert b == true;
  assert i == 2;
}

method TestMfirstNegative2() {
  var v := new int[3];
  v[0] := 1;
  v[1] := 4;
  v[2] := 6;
  var b, i := mfirstNegative(v);
  assert b == false;
}

method TestMfirstNegative21() {
  var v := new int[4];
  v[0] := -1;
  v[1] := 2;
  v[2] := 3;
  v[3] := 4;
  var b, i := mfirstNegative2(v);
  assert b == true;
  assert i == 0;
}

method TestMfirstNegative22() {
  var v := new int[2];
  v[0] := 8;
  v[1] := 9;
  var b, i := mfirstNegative2(v);
  assert b == false;
}
