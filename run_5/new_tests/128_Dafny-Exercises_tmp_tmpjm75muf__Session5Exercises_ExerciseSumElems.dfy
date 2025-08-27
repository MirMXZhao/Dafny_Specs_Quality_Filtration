function SumR(s:seq<int>):int
decreases s
{}

function SumL(s:seq<int>):int
decreases s
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
decreases s,t
ensures SumR(s+t) == SumR(s)+SumR(t)
{}

lemma {:induction s,t} SumByPartsL(s:seq<int>,t:seq<int>)
decreases s,t
ensures SumL(s+t) == SumL(s)+SumL(t)
{}

lemma  {:induction s,i,j} equalSumR(s:seq<int>,i:int,j:int)
decreases j-i
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
{}

lemma equalSumsV() 
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
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
 {equalSumsV();}

method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
{}

method sumElemsB(v:array<int>) returns (sum:int)
ensures sum==SumR(v[0..v.Length])
{}

////////TESTS////////

method TestSumElems1() {
  var v := new int[4];
  v[0] := 1; v[1] := 2; v[2] := 3; v[3] := 4;
  var sum := sumElems(v);
  assert sum == SumR([1, 2, 3, 4]);
}

method TestSumElems2() {
  var v := new int[3];
  v[0] := -1; v[1] := 5; v[2] := -2;
  var sum := sumElems(v);
  assert sum == SumR([-1, 5, -2]);
}

method TestSumElemsB1() {
  var v := new int[4];
  v[0] := 1; v[1] := 2; v[2] := 3; v[3] := 4;
  var sum := sumElemsB(v);
  assert sum == SumR([1, 2, 3, 4]);
}

method TestSumElemsB2() {
  var v := new int[3];
  v[0] := -1; v[1] := 5; v[2] := -2;
  var sum := sumElemsB(v);
  assert sum == SumR([-1, 5, -2]);
}
