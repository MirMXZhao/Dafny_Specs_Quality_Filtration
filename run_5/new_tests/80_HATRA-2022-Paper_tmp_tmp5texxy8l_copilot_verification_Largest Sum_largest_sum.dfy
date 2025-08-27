method largest_sum(nums: array<int>, k: int) returns (sum: int)
    requires nums.Length > 0 
    ensures max_sum_subarray(nums, sum, 0, nums.Length)
{}

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
    requires arr.Length > 0
    requires 0 <= start <= stop <= arr.Length
    reads arr
{}

function Sum_Array(arr: array<int>, start: int, stop: int): int
    requires 0 <= start <= stop <= arr.Length
    decreases stop - start
    reads arr
{}

////////TESTS////////

method TestLargestSum1() {
  var nums := new int[4];
  nums[0] := 1;
  nums[1] := -3;
  nums[2] := 2;
  nums[3] := 1;
  var sum := largest_sum(nums, 0);
  assert sum == 3;
}

method TestLargestSum2() {
  var nums := new int[5];
  nums[0] := -2;
  nums[1] := 1;
  nums[2] := -3;
  nums[3] := 4;
  nums[4] := -1;
  var sum := largest_sum(nums, 0);
  assert sum == 4;
}
