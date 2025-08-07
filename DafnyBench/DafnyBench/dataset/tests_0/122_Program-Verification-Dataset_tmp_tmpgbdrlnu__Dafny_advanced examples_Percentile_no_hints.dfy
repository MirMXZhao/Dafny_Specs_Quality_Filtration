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

method TestSumUpto1() {
  var A := new real[3];
  A[0] := 1.0;
  A[1] := 2.0;
  A[2] := 3.0;
  var result := SumUpto(A, 1);
  assert result == SumUpto(A, 1);
}

method TestSumUpto2() {
  var A := new real[2];
  A[0] := 5.0;
  A[1] := 10.0;
  var result := SumUpto(A, -1);
  assert result == SumUpto(A, -1);
}

method TestSum1() {
  var A := new real[3];
  A[0] := 1.0;
  A[1] := 2.0;
  A[2] := 3.0;
  var result := Sum(A);
  assert result == Sum(A);
}

method TestSum2() {
  var A := new real[1];
  A[0] := 7.5;
  var result := Sum(A);
  assert result == Sum(A);
}

method TestPercentile1() {
  var A := new real[3];
  A[0] := 1.0;
  A[1] := 2.0;
  A[2] := 3.0;
  var total := Sum(A);
  var i := Percentile(50.0, A, total);
  assert -1 <= i < A.Length;
  assert SumUpto(A, i) <= (50.0/100.0) * total;
  assert i+1 < A.Length ==> SumUpto(A, i+1) > (50.0/100.0) * total;
}

method TestPercentile2() {
  var A := new real[2];
  A[0] := 4.0;
  A[1] := 6.0;
  var total := Sum(A);
  var i := Percentile(25.0, A, total);
  assert -1 <= i < A.Length;
  assert SumUpto(A, i) <= (25.0/100.0) * total;
  assert i+1 < A.Length ==> SumUpto(A, i+1) > (25.0/100.0) * total;
}

method TestPercentileNonUniqueAnswer1() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert SumUpto(A, i1) <= (p/100.0) * total;
  assert i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total;
  assert -1 <= i2 < A.Length;
  assert SumUpto(A, i2) <= (p/100.0) * total;
  assert i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total;
  assert i1 != i2;
}

method TestPercentileNonUniqueAnswer2() {
  var p, A, total, i1, i2 := PercentileNonUniqueAnswer();
  assert forall i | 0 <= i < A.Length :: A[i] > 0.0;
  assert 0.0 <= p <= 100.0;
  assert total == Sum(A);
  assert total > 0.0;
  assert -1 <= i1 < A.Length;
  assert SumUpto(A, i1) <= (p/100.0) * total;
  assert i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total;
  assert -1 <= i2 < A.Length;
  assert SumUpto(A, i2) <= (p/100.0) * total;
  assert i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total;
  assert i1 != i2;
}
