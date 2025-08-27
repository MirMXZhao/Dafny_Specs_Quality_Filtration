datatype Interval = Interval(lo: real, hi: real)

predicate contains(i: Interval, r: real) {
  i.lo <= r <= i.hi
}

predicate empty(i: Interval) {
  i.lo > i.hi
}

lemma empty_ok(i: Interval)
  ensures empty(i) <==> !exists r :: contains(i, r)
{}

function min(r1: real, r2: real): real {}

function max(r1: real, r2: real): real {}

function intersect(i1: Interval, i2: Interval): Interval {}

lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

predicate overlap(i1: Interval, i2: Interval) {
  !empty(intersect(i1, i2))
}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
{}

function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{}

lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{}

////////TESTS////////

method TestOverlapWitness1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  var r := overlap_witness(i1, i2);
  assert contains(i1, r) && contains(i2, r);
}

method TestOverlapWitness2() {
  var i1 := Interval(-2.0, 4.0);
  var i2 := Interval(0.0, 8.0);
  var r := overlap_witness(i1, i2);
  assert contains(i1, r) && contains(i2, r);
}
