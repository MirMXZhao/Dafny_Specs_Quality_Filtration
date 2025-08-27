method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{}

predicate is_sorted(nums: seq<int>)
{}

predicate is_sorted_and_distinct(nums: seq<int>)
{}

////////TESTS////////

method TestRemoveDuplicatesFromSortedArray1() {
  var nums := [1, 1, 2, 3, 3, 4];
  var result := remove_duplicates_from_sorted_array(nums);
  assert result == [1, 2, 3, 4];
}

method TestRemoveDuplicatesFromSortedArray2() {
  var nums := [0, 0, 1, 1, 1, 2, 2, 3, 3, 4];
  var result := remove_duplicates_from_sorted_array(nums);
  assert result == [0, 1, 2, 3, 4];
}
