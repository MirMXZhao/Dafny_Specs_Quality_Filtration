method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{}



method TestTwoSum1() {
  var nums := new int[4];
  nums[0] := 2;
  nums[1] := 7;
  nums[2] := 11;
  nums[3] := 15;
  var index1, index2 := twoSum(nums, 9);
  assert index1 != index2;
  assert 0 <= index1 < nums.Length;
  assert 0 <= index2 < nums.Length;
  assert nums[index1] + nums[index2] == 9;
}

method TestTwoSum2() {
  var nums := new int[3];
  nums[0] := 3;
  nums[1] := 2;
  nums[2] := 4;
  var index1, index2 := twoSum(nums, 6);
  assert index1 != index2;
  assert 0 <= index1 < nums.Length;
  assert 0 <= index2 < nums.Length;
  assert nums[index1] + nums[index2] == 6;
}
