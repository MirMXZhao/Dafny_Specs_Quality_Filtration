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
