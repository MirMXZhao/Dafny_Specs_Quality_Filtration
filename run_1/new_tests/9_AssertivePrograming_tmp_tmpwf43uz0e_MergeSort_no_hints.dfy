predicate Sorted(q: seq<int>) {}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
{} 

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{}

// This method replaces the loop body
method {:verify true} MergeLoop(b: array<int>, c: array<int>, d: array<int>,i0: nat , j0: nat)  returns (i: nat, j: nat)
		requires b != c && b != d && b.Length == c.Length + d.Length
		requires Sorted(c[..]) && Sorted(d[..])
		requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
		requires InvSubSet(b[..],c[..],d[..],i0,j0)
		requires InvSorted(b[..],c[..],d[..],i0,j0)
		requires i0 + j0 < b.Length

		modifies b

		ensures i <= c.Length && j <= d.Length && i + j <= b.Length
		ensures InvSubSet(b[..],c[..],d[..],i,j)
		ensures InvSorted(b[..],c[..],d[..],i,j)
		ensures 0 <= c.Length - i < c.Length -

////////TESTS////////

method TestMergeSort1() {
  var a := new int[4] [3, 1, 4, 2];
  var b := MergeSort(a);
  assert b.Length == 4;
  assert Sorted(b[..]);
  assert multiset(a[..]) == multiset(b[..]);
}

method TestMergeSort2() {
  var a := new int[3] [5, 5, 5];
  var b := MergeSort(a);
  assert b.Length == 3;
  assert Sorted(b[..]);
  assert multiset(a[..]) == multiset(b[..]);
}
