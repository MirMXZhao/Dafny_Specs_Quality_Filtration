method max(a:array<int>) returns(max:int)
    requires a != null;
    ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j];
    ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j];
{}