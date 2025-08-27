predicate strictNegative(v:array<int>,i:int,j:int)
reads v
requires 0<=i<=j<=v.Length
{}

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isPermutation(s:seq<int>, t:seq<int>)
{multiset(s)==multiset(t)}

method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
{}

////////TESTS////////

method TestSeparate1() {
  var v := new int[5] [3, -2, 1, -4, 0];
  var i := separate(v);
  assert 0 <= i <= v.Length;
  assert positive(v[0..i]);
  assert strictNegative(v, i, v.Length);
  assert isPermutation(v[0..v.Length], [3, -2, 1, -4, 0]);
}

method TestSeparate2() {
  var v := new int[4] [-1, -3, -5, -2];
  var i := separate(v);
  assert 0 <= i <= v.Length;
  assert positive(v[0..i]);
  assert strictNegative(v, i, v.Length);
  assert isPermutation(v[0..v.Length], [-1, -3, -5, -2]);
}
