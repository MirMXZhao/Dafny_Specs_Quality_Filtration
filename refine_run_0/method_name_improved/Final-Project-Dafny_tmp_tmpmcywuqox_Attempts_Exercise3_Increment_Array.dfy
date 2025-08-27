method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{
  var index : int := 0;
  while(index < a.Length)
    invariant 0 <= index <= a.Length
    invariant forall i :: index <= i < a.Length ==> a[i] == old(a[i])
    invariant forall i :: 0 <= i < index ==> a[i] == old(a[i]) + 1
    decreases a.Length - index     
  {
    assert forall i :: 0 <= i < index ==> a[i] == old(a[i]) + 1;
    assert a[index] == old(a[index]);
    a[index] := a[index] + 1;
    assert forall i :: 0 <= i < index ==> a[i] == old(a[i]) + 1;
    assert a[index] == old(a[index]) + 1;
    index := index+1;   
  }
}