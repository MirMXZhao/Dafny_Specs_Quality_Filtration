method update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures (forall k :: k in m2 ==> k in r)
  ensures (forall k :: k in m1 ==> k in r)
  ensures  (forall k :: k in m2 ==> r[k] == m2[k])
  ensures  (forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k])
  ensures  (forall k :: !(k in m2) && !(k in m1) ==> !(k in r))
{}

////////TESTS////////

method TestUpdateMap1() {
  var m1 := map[1 := "a", 2 := "b", 3 := "c"];
  var m2 := map[2 := "x", 4 := "y"];
  var r := update_map(m1, m2);
  assert r == map[1 := "a", 2 := "x", 3 := "c", 4 := "y"];
}

method TestUpdateMap2() {
  var m1 := map["foo" := 10, "bar" := 20];
  var m2 := map["baz" := 30];
  var r := update_map(m1, m2);
  assert r == map["foo" := 10, "bar" := 20, "baz" := 30];
}
