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