
predicate positive(s:seq<int>)
{}

predicate isEven(i:int)
requires i>=0
{i%2==0}

function CountEven(s:seq<int>):int
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



