class Heap {
  var arr: array<int>

  constructor Heap (input: array<int>)
   ensures this.arr == input {}

  function parent(idx: int): int
  {}

  predicate IsMaxHeap(input: seq<int>)
  {}

  predicate IsAlmostMaxHeap(input: seq<int>, idx: int)
    requires 0 <= idx
  {}

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


method TestHeapify1() {
  var input := new int[5];
  input[0] := 1;
  input[1] := 4;
  input[2] := 3;
  input[3] := 2;
  input[4] := 5;
  var heap := new Heap(input);
  var nidx := heap.heapify(0);
  assert nidx == -1 || (0 < nidx < heap.arr.Length);
}

method TestHeapify2() {
  var input := new int[3];
  input[0] := 10;
  input[1] := 20;
  input[2] := 15;
  var heap := new Heap(input);
  var nidx := heap.heapify(1);
  assert nidx == -1 || (1 < nidx < heap.arr.Length);
}
