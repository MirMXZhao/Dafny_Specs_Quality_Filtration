method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

////////TESTS////////

method TestContainsDuplicate1() {
  var nums := [1, 2, 3, 1];
  var result := contains_duplicate(nums);
  assert result == true;
}

method TestContainsDuplicate2() {
  var nums := [1, 2, 3, 4];
  var result := contains_duplicate(nums);
  assert result == false;
}
