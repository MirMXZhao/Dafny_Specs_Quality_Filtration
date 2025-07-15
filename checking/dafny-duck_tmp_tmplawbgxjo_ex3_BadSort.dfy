predicate sortedbad(s: string)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{
    b := "";
}

method Main(){
    // var a := BadSort("hi"); //this creates an error because BadSort is so terrible
    // is it supposed to 
}