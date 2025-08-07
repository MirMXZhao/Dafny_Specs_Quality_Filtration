method counting_bits(n: int) returns (result: array<int>)
    requires 0 <= n <= 100000
    ensures result.Length == n + 1
    ensures forall i :: 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2
{}

////////TESTS////////

method TestCountingBits1() {
  var result := counting_bits(5);
  assert result[0] == 0;
  assert result[1] == 1;
  assert result[2] == 1;
  assert result[3] == 2;
  assert result[4] == 1;
  assert result[5] == 2;
}

method TestCountingBits2() {
  var result := counting_bits(3);
  assert result[0] == 0;
  assert result[1] == 1;
  assert result[2] == 1;
  assert result[3] == 2;
}

method TestCountingBits3() {
  var result := counting_bits(0);
  assert result[0] == 0;
}
