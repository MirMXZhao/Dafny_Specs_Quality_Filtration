method Max(a:array<nat>)returns(m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..]
{}