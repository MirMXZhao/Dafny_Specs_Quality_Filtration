
method Foo(y: int, x: int) returns (z: int) 
  requires 0 <= y
  ensures z == x*y
{}

function stringToSet(s: string): (r: set<char>)
ensures forall x :: 0 <= x < |s| ==> s[x] in r
{}
//ensures forall a, b :: 0 <= a < b < |s|  ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
// lemma stringSet(s: string)
//    
//   {}


method Main() {}
