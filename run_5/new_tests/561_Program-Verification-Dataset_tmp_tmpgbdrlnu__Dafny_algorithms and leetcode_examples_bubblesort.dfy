function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

function SumRange(lo: int, hi: int): int
  decreases hi - lo
{}

lemma SumRangeNChoose2(n: nat)
  ensures SumRange(0, n) == NChoose2(n)
{}

lemma SumRangeUnrollLeft(lo: int, hi: int)
  decreases hi - lo
  ensures SumRange(lo, hi) ==
          if lo >= hi then 0 else lo + SumRange(lo + 1, hi)
{}

method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
{}

////////TESTS////////

method TestBubbleSort1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  var n := BubbleSort(a);
  assert n <= 6;
}

method TestBubbleSort2() {
  var a := new int[0];
  var n := BubbleSort(a);
  assert n <= 0;
}
