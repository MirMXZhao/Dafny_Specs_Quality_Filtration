method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{}

////////TESTS////////

method TestRemoveDuplicates1() {
  var nums := new int[6];
  nums[0] := 1; nums[1] := 1; nums[2] := 2; nums[3] := 2; nums[4] := 3; nums[5] := 4;
  var num_length := RemoveDuplicates(nums);
  assert num_length == 4;
}

method TestRemoveDuplicates2() {
  var nums := new int[3];
  nums[0] := 5; nums[1] := 5; nums[2] := 5;
  var num_length := RemoveDuplicates(nums);
  assert num_length == 1;
}
