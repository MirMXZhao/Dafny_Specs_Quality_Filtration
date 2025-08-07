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

////////TESTS////////

method TestHeapify1() {
  var input := new int[3];
  input[0] := 1;
  input[1] := 4;
  input[2] := 3;
  var heap := new Heap(input);
  var nidx := heap.heapify(0);
  assert nidx == -1 || (0 < nidx < heap.arr.Length);
  assert nidx == -1 ==> heap.IsMaxHeap(heap.arr[..]);
  assert 0 < nidx < heap.arr.Length ==> heap.IsAlmostMaxHeap(heap.arr[..], nidx);
}

method TestHeapify2() {
  var input := new int[5];
  input[0] := 2;
  input[1] := 8;
  input[2] := 6;
  input[3] := 1;
  input[4] := 3;
  var heap := new Heap(input);
  var nidx := heap.heapify(1);
  assert nidx == -1 || (1 < nidx < heap.arr.Length);
  assert nidx == -1 ==> heap.IsMaxHeap(heap.arr[..]);
  assert 1 < nidx < heap.arr.Length ==> heap.IsAlmostMaxHeap(heap.arr[..], nidx);
}

method TestHeapify3() {
  var input := new int[1];
  input[0] := 5;
  var heap := new Heap(input);
  var nidx := heap.heapify(0);
  assert nidx == -1 || (0 < nidx < heap.arr.Length);
  assert nidx == -1 ==> heap.IsMaxHeap(heap.arr[..]);
  assert 0 < nidx < heap.arr.Length ==> heap.IsAlmostMaxHeap(heap.arr[..], nidx);
}

method TestParent1() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.parent(1);
  assert result == heap.parent(1);
}

method TestParent2() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.parent(5);
  assert result == heap.parent(5);
}

method TestIsMaxHeap1() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.IsMaxHeap([1, 2, 3]);
  assert result == heap.IsMaxHeap([1, 2, 3]);
}

method TestIsMaxHeap2() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.IsMaxHeap([]);
  assert result == heap.IsMaxHeap([]);
}

method TestIsAlmostMaxHeap1() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.IsAlmostMaxHeap([1, 2, 3], 0);
  assert result == heap.IsAlmostMaxHeap([1, 2, 3], 0);
}

method TestIsAlmostMaxHeap2() {
  var input := new int[1];
  input[0] := 1;
  var heap := new Heap(input);
  var result := heap.IsAlmostMaxHeap([5, 4, 3, 2, 1], 2);
  assert result == heap.IsAlmostMaxHeap([5, 4, 3, 2, 1], 2);
}
