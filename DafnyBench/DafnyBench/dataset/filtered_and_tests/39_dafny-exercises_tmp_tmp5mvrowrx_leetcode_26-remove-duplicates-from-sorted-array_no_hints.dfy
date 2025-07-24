
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{}

method Testing() {}

method Main() {
  Testing();
}


method TestRemoveDuplicates1() {
  var nums := new int[5];
  nums[0], nums[1], nums[2], nums[3], nums[4] := 1, 1, 2, 2, 3;
  var num_length := RemoveDuplicates(nums);
  assert num_length == 3;
}

method TestRemoveDuplicates2() {
  var nums := new int[4];
  nums[0], nums[1], nums[2], nums[3] := 0, 0, 1, 1;
  var num_length := RemoveDuplicates(nums);
  assert num_length == 2;
}
