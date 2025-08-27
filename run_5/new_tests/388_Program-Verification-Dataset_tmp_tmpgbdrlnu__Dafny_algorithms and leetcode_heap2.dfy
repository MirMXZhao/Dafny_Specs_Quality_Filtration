class Heap {
  var arr: array<int>

  constructor Heap (input: array<int>)
   ensures this.arr == input {}

  function parent(idx: int): int
  {}

  predicate IsMaxHeap(input: seq<int>)
  {
    forall i :: 0 <= i < |input| ==>
      && (2*i+1 < |input| ==> input[i] >= input[2*i+1])
      && (2*i+2 < |input| ==> input[i] >= input[2*i+2])
  }

  predicate IsAlmostMaxHeap(input: seq<int>, idx: int)
    requires 0 <= idx
  {
    && (forall i :: 0 <= i < |input| ==>
        && (2*i+1 < |input| && i != idx ==> input[i] >= input[2*i+1])
        && (2*i+2 < |input| && i != idx ==> input[i] >= input[2*i+2]))
    && (0 <= parent(idx) < |input| && 2*idx+1 < |input| ==> input[parent(idx)] >= input[2*idx+1])
    && (0 <= parent(idx) < |input| && 2*idx+2 < |input| ==> input[parent(idx)] >= input[2*idx+2])
  }

  method heapify(idx: int)
    returns (nidx: int)
    modifies this, this.arr
    requires 0 <= idx < this.arr.Length
    requires IsAlmostMaxHeap(this.arr[..], idx)
    ensures nidx == -1 || idx < nidx < this.arr.Length
    ensures nidx == -1 ==> IsMaxHeap(this.arr[..])
    ensures idx < nidx < this.arr.Length ==> IsAlmostMaxHeap(this.arr[..], nidx)
  {}
}

////////TESTS////////

method TestHeapify1() {
  var input := new int[7];
  input[0], input[1], input[2], input[3], input[4], input[5], input[6] := 4, 14, 10, 8, 7, 9, 3;
  var heap := new Heap(input);
  var nidx := heap.heapify(0);
  assert nidx == -1;
}

method TestHeapify2() {
  var input := new int[5];
  input[0], input[1], input[2], input[3], input[4] := 1, 10, 8, 5, 6;
  var heap := new Heap(input);
  var nidx := heap.heapify(0);
  assert 0 < nidx < 5;
}
