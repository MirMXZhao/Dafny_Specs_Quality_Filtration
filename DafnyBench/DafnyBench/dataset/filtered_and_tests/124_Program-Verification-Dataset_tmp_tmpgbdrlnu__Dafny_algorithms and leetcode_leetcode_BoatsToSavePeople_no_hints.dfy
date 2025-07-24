/*
function numRescueBoats(people: number[], limit: number): number {};
nums[k++] = i+1;
function binsort(nums: number[], limit: number) {}
*/

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
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= |boatConfigs|
{}

/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/


method TestNumRescueBoats1() {
  var people := [1, 2, 2, 3];
  var limit := 3;
  var boats := numRescueBoats(people, limit);
  assert boats == 3;
}

method TestNumRescueBoats2() {
  var people := [1, 2];
  var limit := 3;
  var boats := numRescueBoats(people, limit);
  assert boats == 1;
}
