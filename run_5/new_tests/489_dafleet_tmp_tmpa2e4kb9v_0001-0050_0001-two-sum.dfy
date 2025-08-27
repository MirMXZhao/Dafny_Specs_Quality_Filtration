ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j
  && nums[i] + nums[j] == target
}

method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
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
