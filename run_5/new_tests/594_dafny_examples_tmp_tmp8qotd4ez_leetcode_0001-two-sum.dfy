predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{}

////////TESTS////////

method TestTwoSum1() {
  var nums := new int[4];
  nums[0], nums[1], nums[2], nums[3] := 2, 7, 11, 15;
  var r := TwoSum(nums, 9);
  assert r == (0, 1);
}

method TestTwoSum2() {
  var nums := new int[3];
  nums[0], nums[1], nums[2] := 3, 2, 4;
  var r := TwoSum(nums, 10);
  assert r == (-1, -1);
}
