function reverse(xs: seq<nat>): seq<nat>
{}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{}

////////TESTS////////

method testreverse1() {
  var xs := [1, 2, 3];
  var result := reverse(xs);
  assert result == [3, 2, 1];
}

method testreverse2() {
  var xs := [5];
  var result := reverse(xs);
  assert result == [5];
}

method testreverse3() {
  var xs := [];
  var result := reverse(xs);
  assert result == [];
}

method testReverseAppendDistr1() {
  var xs := [1, 2];
  var ys := [3, 4];
  ReverseAppendDistr(xs, ys);
  assert reverse(xs + ys) == reverse(ys) + reverse(xs);
}

method testReverseAppendDistr2() {
  var xs := [];
  var ys := [1, 2, 3];
  ReverseAppendDistr(xs, ys);
  assert reverse(xs + ys) == reverse(ys) + reverse(xs);
}

method testReverseInvolution1() {
  var xxs := [1, 2, 3, 4];
  ReverseInvolution(xxs);
  assert reverse(reverse(xxs)) == xxs;
}

method testReverseInvolution2() {
  var xxs := [];
  ReverseInvolution(xxs);
  assert reverse(reverse(xxs)) == xxs;
}
