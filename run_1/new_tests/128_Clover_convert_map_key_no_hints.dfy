method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{}

////////TESTS////////

method TestConvertMapKey1() {
  var inputs := map[1 := true, 2 := false];
  var f := x => x + 10;
  var r := convert_map_key(inputs, f);
  assert r == map[11 := true, 12 := false];
}

method TestConvertMapKey2() {
  var inputs := map[0 := true, 3 := false, 5 := true];
  var f := x => x * 2;
  var r := convert_map_key(inputs, f);
  assert r == map[0 := true, 6 := false, 10 := true];
}
