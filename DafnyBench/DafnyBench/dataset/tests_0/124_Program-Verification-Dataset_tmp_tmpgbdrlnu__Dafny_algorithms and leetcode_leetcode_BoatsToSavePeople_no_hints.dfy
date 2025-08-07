function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{}

predicate isSafeBoat(boat: seq<nat>, limit: nat) {}

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {}

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {}

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {}

predicate sorted(list: seq<int>)
{}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{}

////////TESTS////////

method testsumBoat1() {
  var s := [5];
  var result := sumBoat(s);
  assert result == 5;
}

method testsumBoat2() {
  var s := [3, 7];
  var result := sumBoat(s);
  assert result == 10;
}

method testisSafeBoat1() {
  var boat := [2, 3];
  var result := isSafeBoat(boat, 5);
  assert result == true;
}

method testisSafeBoat2() {
  var boat := [4, 3];
  var result := isSafeBoat(boat, 5);
  assert result == false;
}

method testmultisetAdd1() {
  var ss := [[1, 2], [3]];
  var result := multisetAdd(ss);
  assert result == multiset{1, 2, 3};
}

method testmultisetAdd2() {
  var ss := [[5], [2, 4]];
  var result := multisetAdd(ss);
  assert result == multiset{5, 2, 4};
}

method testmultisetEqual1() {
  var ss := [[1, 2], [3]];
  var xs := [1, 2, 3];
  var result := multisetEqual(ss, xs);
  assert result == true;
}

method testmultisetEqual2() {
  var ss := [[1, 2], [4]];
  var xs := [1, 2, 3];
  var result := multisetEqual(ss, xs);
  assert result == false;
}

method testallSafe1() {
  var boats := [[2, 3], [1]];
  var result := allSafe(boats, 5);
  assert result == true;
}

method testallSafe2() {
  var boats := [[4, 3], [2]];
  var result := allSafe(boats, 5);
  assert result == false;
}

method testsorted1() {
  var list := [1, 2, 3, 4];
  var result := sorted(list);
  assert result == true;
}

method testsorted2() {
  var list := [3, 1, 4, 2];
  var result := sorted(list);
  assert result == false;
}

method testnumRescueBoats1() {
  var people := [1, 2, 2, 3];
  var boats := numRescueBoats(people, 3);
  assert boats == 3;
}

method testnumRescueBoats2() {
  var people := [3, 2, 2, 1];
  var boats := numRescueBoats(people, 3);
  assert boats == 3;
}
