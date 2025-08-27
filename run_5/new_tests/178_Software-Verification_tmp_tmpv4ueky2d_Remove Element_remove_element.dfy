method remove_element(nums: array<int>, val: int) returns (i: int)
    modifies nums
    requires 0 <= nums.Length <= 100
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
    requires 0 <= val <= 100
    ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
{}

////////TESTS////////

method TestRemoveElement1() {
  var nums := new int[4];
  nums[0] := 3;
  nums[1] := 2;
  nums[2] := 2;
  nums[3] := 3;
  var i := remove_element(nums, 3);
  assert i == 2;
}

method TestRemoveElement2() {
  var nums := new int[8];
  nums[0] := 0;
  nums[1] := 1;
  nums[2] := 2;
  nums[3] := 2;
  nums[4] := 3;
  nums[5] := 0;
  nums[6] := 4;
  nums[7] := 2;
  var i := remove_element(nums, 2);
  assert i == 5;
}
