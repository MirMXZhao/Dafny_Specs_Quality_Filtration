predicate sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {}
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {}

method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  {}
  
method Main() {}
