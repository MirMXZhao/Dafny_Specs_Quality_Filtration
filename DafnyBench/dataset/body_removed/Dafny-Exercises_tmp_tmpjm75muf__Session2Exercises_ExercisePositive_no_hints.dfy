predicate positive(s:seq<int>)
{}


method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}

method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{}



