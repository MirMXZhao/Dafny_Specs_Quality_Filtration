method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{}

////////TESTS////////

method TestRemoveElement1() {
  var nums := new int[4];
  nums[0] := 3; nums[1] := 2; nums[2] := 2; nums[3] := 3;
  var newLength := RemoveElement(nums, 3);
  assert newLength == 2;
}

method TestRemoveElement2() {
  var nums := new int[8];
  nums[0] := 0; nums[1] := 1; nums[2] := 2; nums[3] := 2;
  nums[4] := 3; nums[5] := 0; nums[6] := 4; nums[7] := 2;
  var newLength := RemoveElement(nums, 2);
  assert newLength == 5;
}

method TestRemoveElement3() {
  var nums := new int[0];
  var newLength := RemoveElement(nums, 1);
  assert newLength == 0;
}

method TestRemoveElement4() {
  var nums := new int[3];
  nums[0] := 1; nums[1] := 1; nums[2] := 1;
  var newLength := RemoveElement(nums, 1);
  assert newLength == 0;
}
