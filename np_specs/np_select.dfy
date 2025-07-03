//https://numpy.org/doc/stable/reference/generated/numpy.select.html

//Return an array drawn from elements in choicelist, depending on conditions

method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length == choicelist.Length; 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && condlist[0].Length == choicelist[i].Length;
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < n ==> if condlist[i] then ret[i][j] == choicelist[i][j];
{}