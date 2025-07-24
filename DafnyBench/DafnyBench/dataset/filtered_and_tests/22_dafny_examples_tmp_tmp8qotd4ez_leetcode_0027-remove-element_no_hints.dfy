method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{}



method TestRemoveElement1() {
  var nums := new int[4];
  nums[0], nums[1], nums[2], nums[3] := 3, 2, 2, 3;
  var newLength := RemoveElement(nums, 3);
  assert newLength == 2;
}

method TestRemoveElement2() {
  var nums := new int[8];
  nums[0], nums[1], nums[2], nums[3], nums[4], nums[5], nums[6], nums[7] := 0, 1, 2, 2, 3, 0, 4, 2;
  var newLength := RemoveElement(nums, 2);
  assert newLength == 5;
}
