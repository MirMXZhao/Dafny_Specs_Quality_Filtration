method update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures (forall k :: k in m2 ==> k in r)
  ensures (forall k :: k in m1 ==> k in r)
  ensures  (forall k :: k in m2 ==> r[k] == m2[k])
  ensures  (forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k])
  ensures  (forall k :: !(k in m2) && !(k in m1) ==> !(k in r))
{}

////////TESTS////////

method testupdate_map1() {
  var m1 := map[1 := "a", 2 := "b"];
  var m2 := map[2 := "c", 3 := "d"];
  var r := update_map(m1, m2);
  assert r == map[1 := "a", 2 := "c", 3 := "d"];
}

method testupdate_map2() {
  var m1 := map["x" := 10, "y" := 20];
  var m2 := map["z" := 30];
  var r := update_map(m1, m2);
  assert r == map["x" := 10, "y" := 20, "z" := 30];
}

method testupdate_map3() {
  var m1 := map[1 := "a"];
  var m2 := map[int, string];
  var r := update_map(m1, m2);
  assert r == map[1 := "a"];
}
