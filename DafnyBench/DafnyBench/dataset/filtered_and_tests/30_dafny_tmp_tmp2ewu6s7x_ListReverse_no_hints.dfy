function reverse(xs: seq<nat>): seq<nat>
{}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{}



method TestReverse1() {
  var result := reverse([1, 2, 3]);
  assert result == [3, 2, 1];
}

method TestReverse2() {
  var result := reverse([]);
  assert result == [];
}
