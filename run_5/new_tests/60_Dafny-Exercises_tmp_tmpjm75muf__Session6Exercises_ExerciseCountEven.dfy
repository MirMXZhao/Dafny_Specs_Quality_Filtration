predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isEven(i:int)
requires i>=0
{i%2==0}

function CountEven(s:seq<int>):int
decreases s
requires positive(s)
{}

lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
    ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
    ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  {}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{}

////////TESTS////////

method TestMcountEven1() {
  var v := new int[4];
  v[0] := 2;
  v[1] := 4;
  v[2] := 6;
  v[3] := 8;
  var n := mcountEven(v);
  assert n == 4;
}

method TestMcountEven2() {
  var v := new int[3];
  v[0] := 1;
  v[1] := 3;
  v[2] := 5;
  var n := mcountEven(v);
  assert n == 0;
}
