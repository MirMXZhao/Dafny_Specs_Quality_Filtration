function min(v:array<int>,i:int):int
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {}


function countMin(v:array<int>,x:int, i:int):int
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {}


 method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
{}

////////TESTS////////

method TestMin1() {
  var v := new int[3];
  v[0] := 5;
  v[1] := 2;
  v[2] := 8;
  var result := min(v, 3);
  assert result == 2;
}

method TestMin2() {
  var v := new int[2];
  v[0] := 10;
  v[1] := 15;
  var result := min(v, 1);
  assert result == 10;
}

method TestCountMin1() {
  var v := new int[4];
  v[0] := 1;
  v[1] := 3;
  v[2] := 1;
  v[3] := 5;
  var result := countMin(v, 1, 4);
  assert result == 2;
}

method TestCountMin2() {
  var v := new int[3];
  v[0] := 2;
  v[1] := 4;
  v[2] := 6;
  var result := countMin(v, 7, 3);
  assert result == 0;
}

method TestmCountMin1() {
  var v := new int[3];
  v[0] := 1;
  v[1] := 2;
  v[2] := 1;
  var c := mCountMin(v);
  assert c == 2;
}

method TestmCountMin2() {
  var v := new int[4];
  v[0] := 5;
  v[1] := 3;
  v[2] := 8;
  v[3] := 3;
  var c := mCountMin(v);
  assert c == 2;
}
