method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{}

////////TESTS////////

method TestDoubleArray1() {
  var src := new int[3] [1, 2, 3];
  var dst := new int[3] [0, 0, 0];
  DoubleArray(src, dst);
  assert dst[0] == 2;
  assert dst[1] == 4;
  assert dst[2] == 6;
}

method TestDoubleArray2() {
  var src := new int[4] [-1, 0, 5, -3];
  var dst := new int[4] [10, 20, 30, 40];
  DoubleArray(src, dst);
  assert dst[0] == -2;
  assert dst[1] == 0;
  assert dst[2] == 10;
  assert dst[3] == -6;
}
