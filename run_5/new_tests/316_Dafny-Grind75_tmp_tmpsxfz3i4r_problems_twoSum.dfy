predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{}

method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{}

////////TESTS////////

method TestTwoSum1() {
  var nums := [2, 7, 11, 15];
  var target := 9;
  var pair := twoSum(nums, target);
  assert pair == (0, 1);
}

method TestTwoSum2() {
  var nums := [3, 2, 4];
  var target := 6;
  var pair := twoSum(nums, target);
  assert pair == (1, 2);
}
