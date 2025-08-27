function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{}

function Sum(A: array<real>): real
  reads A
{}

method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
{}

method PercentileNonUniqueAnswer() returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0

  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= (p/100.0) * total
  ensures i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total

  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= (p/100.0) * total
  ensures i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total

  ensures i1 != i2
{}

lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0

  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= (p/100.0) * total
  requires i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= (p/100.0) * total
  requires i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total

  decreases if i2 < i1 then 1 else 0

  ensures i1 == i2
{}

lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  ensures SumUpto(A, end1) < SumUpto(A, end2)
{}

////////TESTS////////

method TestPercentile1() {
  var A := new real[3];
  A[0] := 1.0;
  A[1] := 2.0;
  A[2] := 3.0;
  var p := 50.0;
  var total := 6.0;
  var i := Percentile(p, A, total);
  assert i == 0;
}

method TestPercentile2() {
  var A := new real[4];
  A[0] := 2.0;
  A[1] := 1.0;
  A[2] := 1.0;
  A[3] := 1.0;
  var p := 25.0;
  var total := 5.0;
  var i := Percentile(p, A, total);
  assert i == 0;
}

method TestPercentileNonUniqueAnswer1() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert -1 <= i2 < A.Length;
  assert i1 != i2;
}

method TestPercentileNonUniqueAnswer2() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert -1 <= i2 < A.Length;
  assert i1 != i2;
}
