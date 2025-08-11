module {:extern} MapRemove_s {
  function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {}

  method ComputeMapRemove1<K,V>(m: map<K,V>, k:K) 
  returns (m' : map<K,V>)
  ensures m' == MapRemove1(m, k)
}

////////TESTS////////

method TestComputeMapRemove11() {
  var m := map[1 := "a", 2 := "b", 3 := "c"];
  var m' := ComputeMapRemove1(m, 2);
  assert m' == map[1 := "a", 3 := "c"];
}

method TestComputeMapRemove12() {
  var m := map["x" := 10, "y" := 20];
  var m' := ComputeMapRemove1(m, "z");
  assert m' == map["x" := 10, "y" := 20];
}
