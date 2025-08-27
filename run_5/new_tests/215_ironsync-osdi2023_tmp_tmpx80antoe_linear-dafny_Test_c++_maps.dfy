newtype uint32 = i:int | 0 <= i < 0x100000000

datatype map_holder = map_holder(m:map<bool, bool>)

class MyClass {}

method GenericMap<K, V>(m: map<K, V>, n: map<K, V>, o: map<K, V>, a: K, b: K)
    returns (p: map<K, V>, q: map<K, V>, r: map<K, V>)
  requires a in m.Keys && a in n.Keys
  requires b !in m.Keys && b !in o.Keys
  ensures p == m + n && q == n + o && r == o + m
{}

////////TESTS////////

method TestGenericMap1() {
  var m := map[true := false, false := true];
  var n := map[true := true, false := false];
  var o := map[false := true];
  var p, q, r := GenericMap(m, n, o, true, false);
  assert p == map[true := true, false := false];
  assert q == map[true := true, false := true];
  assert r == map[true := false, false := true];
}

method TestGenericMap2() {
  var m := map[1 := 10];
  var n := map[1 := 20, 2 := 30];
  var o := map[3 := 40];
  var p, q, r := GenericMap(m, n, o, 1, 3);
  assert p == map[1 := 20, 2 := 30];
  assert q == map[1 := 20, 2 := 30, 3 := 40];
  assert r == map[1 := 10, 3 := 40];
}
