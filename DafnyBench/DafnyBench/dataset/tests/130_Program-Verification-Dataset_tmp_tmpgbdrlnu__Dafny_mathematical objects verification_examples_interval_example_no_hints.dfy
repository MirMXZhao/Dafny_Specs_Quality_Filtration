datatype Interval = Interval(lo: real, hi: real)

predicate contains(i: Interval, r: real) {}

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

predicate overlap(i1: Interval, i2: Interval) {}

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

method testoverlap1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  var result := overlap(i1, i2);
  assert result == true;
}

method testoverlap2() {
  var i1 := Interval(1.0, 2.0);
  var i2 := Interval(3.0, 4.0);
  var result := overlap(i1, i2);
  assert result == false;
}

method testcontains1() {
  var i := Interval(1.0, 5.0);
  var result := contains(i, 3.0);
  assert result == true;
}

method testcontains2() {
  var i := Interval(1.0, 5.0);
  var result := contains(i, 6.0);
  assert result == false;
}

method testempty1() {
  var i := Interval(5.0, 1.0);
  var result := empty(i);
  assert result == true;
}

method testempty2() {
  var i := Interval(1.0, 5.0);
  var result := empty(i);
  assert result == false;
}

method testempty_ok1() {
  var i := Interval(5.0, 1.0);
  empty_ok(i);
}

method testempty_ok2() {
  var i := Interval(1.0, 5.0);
  empty_ok(i);
}

method testmin1() {
  var result := min(3.0, 7.0);
  assert result == 3.0;
}

method testmin2() {
  var result := min(7.0, 3.0);
  assert result == 3.0;
}

method testmax1() {
  var result := max(3.0, 7.0);
  assert result == 7.0;
}

method testmax2() {
  var result := max(7.0, 3.0);
  assert result == 7.0;
}

method testintersect1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  var result := intersect(i1, i2);
  assert result.lo == 3.0 && result.hi == 5.0;
}

method testintersect2() {
  var i1 := Interval(1.0, 2.0);
  var i2 := Interval(3.0, 4.0);
  var result := intersect(i1, i2);
  assert result.lo > result.hi;
}

method testintersect_ok1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  intersect_ok(i1, i2);
}

method testintersect_ok2() {
  var i1 := Interval(1.0, 2.0);
  var i2 := Interval(3.0, 4.0);
  intersect_ok(i1, i2);
}

method testoverlap_ok1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  overlap_ok(i1, i2);
}

method testoverlap_ok2() {
  var i1 := Interval(1.0, 2.0);
  var i2 := Interval(3.0, 4.0);
  overlap_ok(i1, i2);
}

method testunion1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  var result := union(i1, i2);
  assert result.lo == 1.0 && result.hi == 7.0;
}

method testunion2() {
  var i1 := Interval(2.0, 4.0);
  var i2 := Interval(1.0, 6.0);
  var result := union(i1, i2);
  assert result.lo == 1.0 && result.hi == 6.0;
}

method testunion_ok1() {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  union_ok(i1, i2);
}

method testunion_ok2() {
  var i1 := Interval(2.0, 4.0);
  var i2 := Interval(1.0, 6.0);
  union_ok(i1, i2);
}

method testoverlap_witness1() returns (r: real) {
  var i1 := Interval(1.0, 5.0);
  var i2 := Interval(3.0, 7.0);
  r := overlap_witness(i1, i2);
}

method testoverlap_witness2() returns (r: real) {
  var i1 := Interval(2.0, 6.0);
  var i2 := Interval(4.0, 8.0);
  r := overlap_witness(i1, i2);
}
