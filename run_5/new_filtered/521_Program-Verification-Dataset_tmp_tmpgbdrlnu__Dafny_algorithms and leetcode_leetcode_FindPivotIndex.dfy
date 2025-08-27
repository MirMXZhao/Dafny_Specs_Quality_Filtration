function sum(nums: seq<int>): int {}


function sumUp(nums: seq<int>): int {}

lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{}

lemma sumsEqual(nums: seq<int>)
  decreases |nums|
  ensures sum(nums) == sumUp(nums)
{}


method  FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{}