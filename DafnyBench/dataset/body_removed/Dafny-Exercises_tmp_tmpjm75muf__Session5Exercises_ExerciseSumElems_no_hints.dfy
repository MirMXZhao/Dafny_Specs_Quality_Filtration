function SumR(s:seq<int>):int
{}

function SumL(s:seq<int>):int
{}


lemma concatLast(s:seq<int>,t:seq<int>)
requires t!=[]
ensures (s+t)[..|s+t|-1] == s+(t[..|t|-1])
{}
lemma concatFirst(s:seq<int>,t:seq<int>)
requires s!=[]
ensures (s+t)[1..] == s[1..]+t
{}

lemma {:induction s,t} SumByPartsR(s:seq<int>,t:seq<int>)
ensures SumR(s+t) == SumR(s)+SumR(t)
{}


lemma {:induction s,t} SumByPartsL(s:seq<int>,t:seq<int>)
ensures SumL(s+t) == SumL(s)+SumL(t)
//Prove this
{}




lemma  {:induction s,i,j} equalSumR(s:seq<int>,i:int,j:int)
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
//Prove this
{}


lemma equalSumsV() 
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 //proving the forall
  {}


function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {SumR(v[c..f])}


lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
  ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
  ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
 // ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
 {equalSumsV();}
  

method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)

{}

method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
{}







