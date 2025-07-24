method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{}

method TestConvertMapKey1() {
  var inputs := map[1 := true, 3 := false];
  var f := x => x * 2;
  var r := convert_map_key(inputs, f);
  assert r == map[2 := true, 6 := false];
}

method TestConvertMapKey2() {
  var inputs := map[0 := false, 2 := true, 4 := false];
  var f := x => x + 1;
  var r := convert_map_key(inputs, f);
  assert r == map[1 := false, 3 := true, 5 := false];
}
