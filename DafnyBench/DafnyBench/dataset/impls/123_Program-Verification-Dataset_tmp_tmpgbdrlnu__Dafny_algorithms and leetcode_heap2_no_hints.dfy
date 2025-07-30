class Heap {
  var arr: array<int>

  constructor Heap (input: array<int>)
   ensures this.arr == input {
    this.arr := input;
  }

  function parent(idx: int): int
  {
    (idx - 1) / 2
  }

  predicate IsMaxHeap(input: seq<int>)
  {
    forall i :: 0 <= i < |input| ==> 
      (2*i + 1 >= |input| || input[i] >= input[2*i + 1]) &&
      (2*i + 2 >= |input| || input[i] >= input[2*i + 2])
  }

  predicate IsAlmostMaxHeap(input: seq<int>, idx: int)
    requires 0 <= idx
  {
    forall i :: 0 <= i < |input| && i != idx ==> 
      (2*i + 1 >= |input| || input[i] >= input[2*i + 1]) &&
      (2*i + 2 >= |input| || input[i] >= input[2*i + 2])
  }

  method heapify(idx: int)
    returns (nidx: int)
    modifies this, this.arr
    requires 0 <= idx < this.arr.Length
    requires IsAlmostMaxHeap(this.arr[..], idx)
    ensures nidx == -1 || idx < nidx < this.arr.Length
    ensures nidx == -1 ==> IsMaxHeap(this.arr[..])
    ensures idx < nidx < this.arr.Length ==> IsAlmostMaxHeap(this.arr[..], nidx)
  {
    var left := 2 * idx + 1;
    var right := 2 * idx + 2;
    var largest := idx;
    
    if left < this.arr.Length && this.arr[left] > this.arr[largest] {
      largest := left;
    }
    
    if right < this.arr.Length && this.arr[right] > this.arr[largest] {
      largest := right;
    }
    
    if largest != idx {
      var temp := this.arr[idx];
      this.arr[idx] := this.arr[largest];
      this.arr[largest] := temp;
      nidx := largest;
    } else {
      nidx := -1;
    }
  }
}

// method TestHeapify1() {
//   var input := new int[5];
//   input[0] := 1;
//   input[1] := 4;
//   input[2] := 3;
//   input[3] := 2;
//   input[4] := 5;
//   var heap := new Heap(input);
//   var nidx := heap.heapify(0);
//   assert nidx == -1 || (0 < nidx < heap.arr.Length);
// }

// method TestHeapify2() {
//   var input := new int[3];
//   input[0] := 10;
//   input[1] := 20;
//   input[2] := 15;
//   var heap := new Heap(input);
//   var nidx := heap.heapify(1);
//   assert nidx == -1 || (1 < nidx < heap.arr.Length);
// }