predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i,j::0<=i<=j<|s| ==> s[i]==s[j]
{}

lemma equivalenceEqualtoFirst(s:seq<int>)
requires s!=[]
ensures allEqual(s) <==> (forall i::0<=i<|s| ==> s[0]==s[i])
{}

lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
ensures (allEqual(s) <== forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
{}

method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{}

method mallEqual2(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{}

method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{}

method mallEqual4(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{}

method mallEqual5(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{}

////////TESTS////////

method TestmallEqual11() {
  var v := new int[3];
  v[0] := 5;
  v[1] := 5;
  v[2] := 5;
  var b := mallEqual1(v);
  assert b == true;
}

method TestmallEqual12() {
  var v := new int[3];
  v[0] := 1;
  v[1] := 2;
  v[2] := 1;
  var b := mallEqual1(v);
  assert b == false;
}

method TestmallEqual21() {
  var v := new int[4];
  v[0] := 7;
  v[1] := 7;
  v[2] := 7;
  v[3] := 7;
  var b := mallEqual2(v);
  assert b == true;
}

method TestmallEqual22() {
  var v := new int[2];
  v[0] := 3;
  v[1] := 8;
  var b := mallEqual2(v);
  assert b == false;
}

method TestmallEqual31() {
  var v := new int[1];
  v[0] := 42;
  var b := mallEqual3(v);
  assert b == true;
}

method TestmallEqual32() {
  var v := new int[5];
  v[0] := 1;
  v[1] := 1;
  v[2] := 2;
  v[3] := 1;
  v[4] := 1;
  var b := mallEqual3(v);
  assert b == false;
}

method TestmallEqual41() {
  var v := new int[0];
  var b := mallEqual4(v);
  assert b == true;
}

method TestmallEqual42() {
  var v := new int[3];
  v[0] := 9;
  v[1] := 9;
  v[2] := 10;
  var b := mallEqual4(v);
  assert b == false;
}

method TestmallEqual51() {
  var v := new int[2];
  v[0] := -3;
  v[1] := -3;
  var b := mallEqual5(v);
  assert b == true;
}

method TestmallEqual52() {
  var v := new int[4];
  v[0] := 0;
  v[1] := 1;
  v[2] := 0;
  v[3] := 0;
  var b := mallEqual5(v);
  assert b == false;
}
