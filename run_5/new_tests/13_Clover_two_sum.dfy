method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{}

////////TESTS////////

method TestTwoSum1() {
  var nums := new int[4];
  nums[0] := 2;
  nums[1] := 7;
  nums[2] := 11;
  nums[3] := 15;
  var i, j := twoSum(nums, 9);
  assert i == 0;
  assert j == 1;
}

method TestTwoSum2() {
  var nums := new int[3];
  nums[0] := 3;
  nums[1] := 2;
  nums[2] := 4;
  var i, j := twoSum(nums, 6);
  assert i == 1;
  assert j == 2;
}
