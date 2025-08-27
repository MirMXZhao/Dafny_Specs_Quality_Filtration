method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max >= 1
{}

function find_max(x: int, y: int): int
{}

////////TESTS////////

method TestLongestIncreasingSubsequence1() {
    var nums := new int[4];
    nums[0] := 1;
    nums[1] := 3;
    nums[2] := 2;
    nums[3] := 4;
    var max := longest_increasing_subsequence(nums);
    assert max == 3;
}

method TestLongestIncreasingSubsequence2() {
    var nums := new int[5];
    nums[0] := 5;
    nums[1] := 4;
    nums[2] := 3;
    nums[3] := 2;
    nums[4] := 1;
    var max := longest_increasing_subsequence(nums);
    assert max == 1;
}

method TestFindMax1() {
    var result := find_max(5, 3);
    assert result == 5;
}

method TestFindMax2() {
    var result := find_max(-2, 7);
    assert result == 7;
}
